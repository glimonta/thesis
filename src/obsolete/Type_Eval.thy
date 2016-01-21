theory Type_Eval
imports SmallStep Type_Checker 
begin

    lemma (in -) o2b_assert[simp]: "o2b (Exp.assert \<Phi>) \<longleftrightarrow> \<Phi>"
      by (cases \<Phi>) auto

    lemma [simp]: "(\<forall>x. \<not>is_res m x) \<Longrightarrow> cp_err m \<noteq> return v"  
      by (cases m) auto

  type_synonym memtype = "nat \<rightharpoonup> type"


  context program_loc
  begin

    context
      fixes MT :: memtype
      fixes \<mu> :: mem
    begin
      definition tm_addr :: "type \<Rightarrow> addr \<Rightarrow> bool" where 
        "tm_addr \<equiv> \<lambda>T (i,_). MT i = Some T"

      fun tm_val :: "type \<Rightarrow> val \<Rightarrow> bool" where
        "tm_val TInt (I _) \<longleftrightarrow> True"
      | "tm_val TNull NullVal \<longleftrightarrow> True"
      | "tm_val (TPtr T) NullVal \<longleftrightarrow> True"
      | "tm_val (TPtr T) (A addr) \<longleftrightarrow> tm_addr T addr"
      | "tm_val _ _ \<longleftrightarrow> False"
    
      fun tm_val_option :: "type \<Rightarrow> val option \<Rightarrow> bool" where
        "tm_val_option T None \<longleftrightarrow> True"
      | "tm_val_option T (Some v) \<longleftrightarrow> tm_val T v"  

      lemma tm_val_int_simps[simp]:
        "tm_val T (I i) \<longleftrightarrow> T=TInt" by (cases T) auto


      definition tm_mem :: bool where "tm_mem \<equiv> 
        dom MT = {0..<length \<mu>} 
          \<and> (\<forall>i j b. i<length \<mu> \<and> \<mu>!i = Some b \<and> j<length b \<longrightarrow> tm_val_option (the (MT i)) (b!j))"


      definition tm_valuation :: "typing \<Rightarrow> valuation \<Rightarrow> bool" where
        "tm_valuation TE \<sigma> \<equiv> 
            (dom TE = dom \<sigma>) 
          \<and> (\<forall>x T vo. TE x = Some T \<and> \<sigma> x = Some vo \<longrightarrow> tm_val_option T vo)"

      abbreviation "tm_globals \<equiv> tm_valuation GT"


      definition tm_frame :: "fun_decl \<Rightarrow> stack_frame \<Rightarrow> bool"
        where "tm_frame \<equiv> \<lambda>fdecl (c,l,_). 
          tm_com fdecl c 
        \<and> tm_valuation (LT fdecl) l"

      definition rloc_compat :: "fun_decl \<Rightarrow> (fun_decl \<times> stack_frame) \<Rightarrow> bool" where
        "rloc_compat \<equiv> \<lambda>fdecl0 (fdecl1,(_,_,rloc)). case rloc of
          Invalid \<Rightarrow> True
        | Ar (i,j) \<Rightarrow> 
            (case (MT i, fun_decl.rtype fdecl0) of
              (Some T,Some T') \<Rightarrow> T=T'
            | _ \<Rightarrow> False)
        | Vr x \<Rightarrow> 
            (case (read_varty fdecl1 x, fun_decl.rtype fdecl0) of
              (Some T, Some T') \<Rightarrow> T=T'
            | _ \<Rightarrow> False  
            )
        "

      definition tm_stack :: "fun_decl list \<Rightarrow> stack_frame list \<Rightarrow> bool" where
        "tm_stack stkT stk \<equiv> 
          list_all2 tm_frame stkT stk \<and>
          (\<forall>i. 1\<le>i \<and> i<length stk \<longrightarrow> rloc_compat (stkT!(i-1)) (stkT!i,stk!i))
        "

      definition tm :: "valuation \<Rightarrow> fun_decl list \<Rightarrow> stack_frame list \<Rightarrow> bool" where
        "tm \<gamma> stkT stk \<equiv> tm_mem \<and> tm_globals \<gamma> \<and> tm_stack stkT stk"

    end      

    definition WT :: "state \<Rightarrow> bool" 
      where "WT \<equiv> \<lambda>(stk,\<gamma>,\<mu>). \<exists>MT stkT. tm MT \<mu> \<gamma> stkT stk"

  
    definition "tm_slink MT fd stkT stk \<equiv> 
        list_all2 (tm_frame MT) stkT stk
      \<and> (\<forall>i. Suc 0 \<le> i \<and> i < Suc (length stk) \<longrightarrow>
           program_loc.rloc_compat p MT
            ((fd # stkT) ! (i - Suc 0))
            (stkT ! (i - Suc 0), stk ! (i - Suc 0)))"
  

    definition WTv  
      where "WTv MT \<mu> \<gamma> fd stkT c l stk \<equiv> \<forall>rloc. tm MT \<mu> \<gamma> (fd#stkT) ((c,l,rloc)#stk)"

    lemma WTv_alt: "WTv MT \<mu> \<gamma> fd stkT c l stk \<longleftrightarrow> 
      tm_mem MT \<mu>
      \<and> tm_globals MT \<gamma>
      \<and> tm_com fd c
      \<and> tm_valuation MT (LT fd) l
      \<and> tm_slink MT fd stkT stk"  
      by (auto simp: WTv_def tm_def tm_stack_def tm_frame_def list_all2_Cons2 tm_slink_def)

  end    

  locale focus_visible_loc = program_loc p for p +
    fixes MT :: memtype and \<mu> :: mem 
    and \<gamma> :: valuation 
    and fd :: fun_decl and c :: com and l :: valuation 
    and stkT :: "fun_decl list" and stk :: "stack_frame list"

    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
  begin  
    lemma 
          tm_mem: "tm_mem MT \<mu>" 
      and tm_globals: "tm_globals MT \<gamma>"
      and tm_com: "tm_com fd c" 
      and tm_locals: "tm_valuation MT (LT fd) l"
      and tm_slink: "tm_slink MT fd stkT stk"
      using WTv unfolding WTv_alt by auto

  end

  context program_loc begin

  lemma tycheck_com_step1:
    assumes "cfg c1 (et,en,tr) c2"
    assumes "o2b (tycheck_com fd c1)"
    shows "o2b (tycheck_com fd c2)"
    using assms
    unfolding o2b_alt
    apply induction
    apply (simp_all split: Option.bind_splits)
    done

  lemma tycheck_com_step2:
    assumes "cfg c1 (et,en,tr) c2"
    assumes "et\<noteq>ET_Return"
    assumes "tm_com_ret fd c1"
    shows "tm_com_ret fd c2"
    using assms
    apply (induction c1 "(et,en,tr)" c2)
    by auto

  (*lemma tycheck_com_step:
    assumes "cfg c1 (en,tr) c2"
    assumes "(\<forall>e. tr \<noteq> tr_return e) \<and> tr \<noteq> tr_return_void"
    assumes "tm_com fd c1"
    shows "tm_com fd c2"
    using tycheck_com_step1 tycheck_com_step2 assms by blast
  *)  

  lemma ty_cfg_cases[consumes 2, case_names assign assignl skip ifT ifF free return returnv calll call callv]:
    assumes "cfg c1 (et,en,tr) c2"
    assumes "o2b (tycheck_com fd c1)"
    obtains 
      x a T where  "et=ET_Intra" "en=en_always" "tr = tr_assign x a" "read_varty fd x = Some T" "tyeval fd a = Some T" 
    | le a T where "et=ET_Intra" "en=en_always" "tr = tr_assignl le a" "tyeval_l fd le = Some T" "tyeval fd a = Some T"
    |            "et=ET_Intra" "en=en_always" "tr=tr_id" 
    | b where    "et=ET_Intra" "en=en_pos b"  "tr=tr_eval b" "tyeval fd b = Some TInt" 
    | b where    "et=ET_Intra" "en=en_neg b"  "tr=tr_eval b" "tyeval fd b = Some TInt" 
    | e T where    "et=ET_Intra" "en=en_always" "tr=tr_free e" "tyeval fd e = Some T" "is_TPtr T" 
    | e T where    "et=ET_Return" "en=en_always" "tr=tr_return e" "RT fd = Some T" "tyeval fd e = Some T"
    |            "et=ET_Return" "en=en_always" "tr=tr_return_void" "RT fd = None"
    | le f ps where "et=ET_Call" "en=en_always" "tr=tr_callfunl proc_table le f ps" "o2b (fun_compatl fd le f ps)" 
    | x f ps  where "et=ET_Call" "en=en_always" "tr=tr_callfun proc_table x f ps" "o2b (fun_compat fd x f ps)" 
    | f ps    where "et=ET_Call" "en=en_always" "tr=tr_callfunv proc_table f ps" "o2b (fun_compatv fd f ps)" 
  proof -
    from assms have "o2b (tycheck_com fd c1)" by simp
    from assms that show ?thesis
      apply (induct c1 "(et,en,tr)" c2)
      apply (clarsimp split: Option.bind_splits; blast)+
      done
  qed    


  lemma focus_visible[consumes 3, case_names frame]: 
    assumes WT: "WT s"
    assumes "\<not> is_empty_stack s"
    assumes "c = com_of s"
    obtains stk stkT fd l rloc \<gamma> \<mu> MT where 
      "s=((c,l,rloc)#stk,\<gamma>,\<mu>)" 
      "focus_visible_loc p MT \<mu> \<gamma> fd c l stkT stk"
      using assms unfolding WT_def
      apply (cases s rule: com_of.cases)
  proof clarsimp
    fix stk stkT' fd l rloc \<gamma> \<mu> MT
    assume [simp]: "s=((c,l,rloc)#stk,\<gamma>,\<mu>)"
    and TM: "tm MT \<mu> \<gamma> stkT' ((c,l,rloc)#stk)"
    then obtain stkT fd where [simp]: "stkT' = fd#stkT"
      by (auto simp: tm_def tm_stack_def list_all2_Cons2)

    show thesis
      apply rule
      apply simp
      apply unfold_locales
      using TM
      unfolding WTv_alt tm_def tm_stack_def tm_slink_def tm_frame_def
      by auto
  qed simp       

  lemma (in focus_visible_loc) LT_None[simp]: 
    "LT fd x = None \<Longrightarrow> l x = None"
    using tm_locals
    unfolding tm_valuation_def
    by auto

  lemma (in focus_visible_loc) GT_None[simp]: 
    "GT x = None \<Longrightarrow> \<gamma> x = None"
    using tm_globals
    unfolding tm_valuation_def
    by auto

  lemma (in focus_visible_loc) LT_SomeE: 
    assumes "LT fd x = Some T" 
    obtains vo where "l x = Some vo" "tm_val_option MT T vo"
    using assms tm_locals
    unfolding tm_valuation_def
    by (force simp: dom_def)

  lemma (in focus_visible_loc) GT_SomeE: 
    assumes "GT x = Some T" 
    obtains vo where "\<gamma> x = Some vo" "tm_val_option MT T vo"
    using assms tm_globals
    unfolding tm_valuation_def
    by (force simp: dom_def)
    


  lemma (in focus_visible_loc) read_varty_cases[consumes 1, case_names local global]:   
    assumes "program_loc.read_varty p fd x = Some T"
    obtains vo where "l x = Some vo" and "tm_val_option MT T vo"
      | vo where "l x = None" and "\<gamma> x = Some vo" and "tm_val_option MT T vo"
    using assms  
    unfolding read_varty_def
    by (auto split: option.splits elim: GT_SomeE LT_SomeE)


  lemmas read_varty_cases_raw = focus_visible_loc.read_varty_cases[unfolded focus_visible_loc_def]  

  abbreviation nte_spec :: "('a, chloe_error) error \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where
    "nte_spec \<equiv> \<lambda>m P. e_spec P (\<lambda>e. \<not> is_EStatic e) False m"

  (*lemma [intro,simp]: "\<not>(nte_spec type_error post)" by simp

  lemma nte_spec_bind:
    assumes "nte_spec m p1"
    assumes "\<And>x. m=return x \<Longrightarrow> p1 x \<Longrightarrow> nte_spec (f x) post"
    shows "nte_spec (Error_Monad.bind m f) post"
    using assms
    by (cases m) auto

  lemma nte_spec_assert[simp]: "nte_spec (assert \<Phi> e) post 
    \<longleftrightarrow> (if e=EStatic EType then \<Phi> \<and> post () else \<Phi>\<longrightarrow>post())"  
    unfolding assert_def by (auto)
  *)  

  lemma plus_val_spec[e_vcg]:
    assumes "tm_val MT TInt v1"  
    assumes "tm_val MT' TInt v2"  
    shows "nte_spec (plus_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: plus_val.cases; simp?)
    by e_vcg

  lemma tm_addr_of: 
    "NO_MATCH 0 y \<Longrightarrow> tm_addr MT T (x, y) \<longleftrightarrow> tm_addr MT T (x, 0)"
    "NO_MATCH (i,j) addr \<Longrightarrow> tm_addr MT T addr \<longleftrightarrow> (\<exists>i j. addr=(i,j) \<and> tm_addr MT T (i,j))"
    by (auto simp: tm_addr_def)

  (* TODO: Move *)  
  lemma (in -) map_leD[intro?, elim]: "m \<subseteq>\<^sub>m m' \<Longrightarrow> m x = Some v \<Longrightarrow> m' x = Some v"  
    by (auto simp: map_le_def dom_def)

  declare (in -) map_le_refl[intro!]  

  lemma tm_addr_mono[simp, intro]: "\<lbrakk> MT \<subseteq>\<^sub>m MT' \<rbrakk> \<Longrightarrow> tm_addr MT T a \<Longrightarrow> tm_addr MT' T a"
    by (auto simp: tm_addr_def)

  lemma assert_valid_addr_spec[e_vcg]: "nte_spec (assert_valid_addr \<mu> addr) 
    (\<lambda>_. let (i,j) = addr in 0\<le>i \<and> i<length \<mu> \<and> \<mu>!i\<noteq>None \<and> 0\<le>j \<and> nat j \<le> length (the (\<mu>!i)))"
    unfolding assert_valid_addr_def Let_def mem_get_block_def
    by e_vcg

  lemma ofs_addr_spec[e_vcg]: "nte_spec (ofs_addr \<mu> addr ofs) (\<lambda>(i,j). i=fst addr)"  
    apply (cases "(\<mu>,addr,ofs)" rule: ofs_addr.cases; simp add: Let_def)
    by e_vcg

  lemma plus_val_spec'[e_vcg]:
    assumes "tm_val MT (TPtr T) v1"  
    assumes "tm_val MT' TInt v2"  
    assumes "MT \<subseteq>\<^sub>m MT'"
    shows "nte_spec (plus_val \<mu> v1 v2) (tm_val MT' (TPtr T))"
  proof -
    note [simp] = tm_addr_of
    show ?thesis
      using assms
      apply (cases "(\<mu>,v1,v2)" rule: plus_val.cases)
      apply (simp_all)
      apply e_vcg
      done
  qed    


  lemma subst_val_spec[e_vcg]:
    assumes "tm_val MT TInt v1"  
    assumes "tm_val MT' TInt v2"  
    shows "nte_spec (subst_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: subst_val.cases)
    apply simp_all
    by e_vcg

  lemma subst_val_spec'[e_vcg]:
    assumes "tm_val MT (TPtr T) v1"  
    assumes "tm_val MT' TInt v2"  
    assumes "MT \<subseteq>\<^sub>m MT'"
    shows "nte_spec (subst_val \<mu> v1 v2) (tm_val MT' (TPtr T))"
  proof -
    note [simp] = tm_addr_of
    show ?thesis
      using assms
      apply (cases "(\<mu>,v1,v2)" rule: subst_val.cases)
      apply (simp_all)
      apply e_vcg
      done
  qed    

  lemma subst_val_spec''[e_vcg]:
    assumes "tm_val MT (TPtr T) v1"  
    assumes "tm_val MT' (TPtr T) v2"  
    assumes "MT \<subseteq>\<^sub>m MT'"
    shows "nte_spec (subst_val \<mu> v1 v2) (tm_val MT' (TInt))"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: subst_val.cases)
    apply simp_all
    apply e_vcg
    done


  lemma minus_val_spec[e_vcg]:
    assumes "tm_val MT TInt v"  
    shows "nte_spec (minus_val v) (tm_val MT TInt)"
    using assms
    apply (cases v rule: minus_val.cases)
    apply simp_all by e_vcg

  lemma not_val_spec[e_vcg]:
    assumes "tm_val MT TInt v"  
    shows "nte_spec (not_val v) (tm_val MT TInt)"
    using assms
    apply (cases v)
    unfolding not_val_def from_bool_def
    by simp_all

  lemma div_val_spec[e_vcg]:
    assumes "tm_val MT TInt v1"  
    assumes "tm_val MT' TInt v2"  
    shows "nte_spec (div_val v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(v1,v2)" rule: div_val.cases)
    apply simp_all
    apply clarsimp
    apply e_vcg
    done

  lemma mod_val_spec[e_vcg]:
    assumes "tm_val MT TInt v1"  
    assumes "tm_val MT' TInt v2"  
    shows "nte_spec (mod_val v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(v1,v2)" rule: mod_val.cases)
    apply simp_all
    by clarsimp e_vcg

  lemma mult_val_spec[e_vcg]:
    assumes "tm_val MT TInt v1"  
    assumes "tm_val MT' TInt v2"  
    shows "nte_spec (mult_val v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(v1,v2)" rule: mult_val.cases)
    apply simp_all
    by clarsimp e_vcg

  lemma less_val_spec[e_vcg]:
    assumes "tm_val MT TInt v1"  
    assumes "tm_val MT' TInt v2"  
    shows "nte_spec (less_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: less_val.cases)
    apply (simp_all add: from_bool_def)
    done

  lemma less_val_spec'[e_vcg]:
    assumes "tm_val MT (TPtr T) v1"  
    assumes "tm_val MT' (TPtr T) v2"  
    shows "nte_spec (less_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: less_val.cases)
    apply (simp_all add: from_bool_def)
    by (safe; e_vcg)

  lemma to_bool_spec[e_vcg]:
    assumes "tm_val MT TInt v"  
    shows "nte_spec (to_bool v) (\<lambda>_. True)"
    using assms
    apply (cases v rule: to_bool.cases)
    apply simp_all
    done


  lemma eq_val_spec[e_vcg]:
    assumes "tm_val MT TInt v1"  
    assumes "tm_val MT' TInt v2"  
    shows "nte_spec (eq_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: eq_val.cases)
    apply simp_all
    done

  lemma eq_val_spec'[e_vcg]:
    assumes "tm_val MT (TPtr T) v1"  
    assumes "tm_val MT' (TPtr T) v2"  
    shows "nte_spec (eq_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: eq_val.cases)
    apply simp_all
    apply (safe; e_vcg)+
    done

  lemma eq_val_spec''[e_vcg]:
    assumes "tm_val MT (TPtr T) v1"  
    assumes "tm_val MT' TNull v2"  
    shows "nte_spec (eq_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: eq_val.cases)
    apply simp_all
    by e_vcg

  lemma eq_val_spec'''[e_vcg]:
    assumes "tm_val MT TNull v1"  
    assumes "tm_val MT' (TPtr T) v2"  
    shows "nte_spec (eq_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: eq_val.cases)
    apply simp_all
    by e_vcg

  lemma eq_val_spec''''[e_vcg]:
    assumes "tm_val MT TNull v1"  
    assumes "tm_val MT' TNull v2"  
    shows "nte_spec (eq_val \<mu> v1 v2) (tm_val MT' TInt)"
    using assms
    apply (cases "(\<mu>,v1,v2)" rule: eq_val.cases)
    by simp_all

  lemma (in -) map_le_upd_new[intro, simp]: "\<lbrakk>k\<notin>dom m\<rbrakk> \<Longrightarrow> m \<subseteq>\<^sub>m m(k:=v)"  
    unfolding map_le_def dom_def
    by simp

  lemma tm_mem_alloc_map_le: "tm_mem MT \<mu> \<Longrightarrow> MT \<subseteq>\<^sub>m MT(length \<mu> \<mapsto> T)"    
    unfolding tm_mem_def by auto

  lemma tm_val_MT_mono: "MT \<subseteq>\<^sub>m MT' \<Longrightarrow> tm_val MT T v \<Longrightarrow> tm_val MT' T v"   
    by (cases "(T,v)" rule: tm_val.cases) auto

  lemma tm_val_option_MT_mono: "MT \<subseteq>\<^sub>m MT' \<Longrightarrow> tm_val_option MT T v \<Longrightarrow> tm_val_option MT' T v"   
    by (cases "(T,v)" rule: tm_val_option.cases) (auto simp: tm_val_MT_mono)

  lemma tm_valuation_MT_mono: "MT \<subseteq>\<^sub>m MT' \<Longrightarrow> tm_valuation MT Ts vs \<Longrightarrow> tm_valuation MT' Ts vs"  
    unfolding tm_valuation_def by (auto simp: tm_val_option_MT_mono)

  lemma tm_mem_alloc_pres: 
    assumes "tm_mem MT \<mu>"
    shows "tm_mem (MT(length \<mu> \<mapsto> T)) (\<mu> @ [Some (replicate (nat (sint i)) None)])"  
    using assms unfolding tm_mem_def
    using tm_val_option_MT_mono[OF tm_mem_alloc_map_le[OF assms]]
    by (auto simp: nth_append)

  (* TODO: Move *)  
  lemma (in -) list_all2_mono:
    assumes "list_all2 R l1 l2"
    assumes "\<And>x y. (x,y)\<in>set (zip l1 l2) \<Longrightarrow> R x y \<Longrightarrow> R' x y"
    shows "list_all2 R' l1 l2"
    using assms
    by (metis case_prodI2 list_all2_iff old.prod.case)
    

  thm subsetD  


  lemma rloc_compat_mono: "MT \<subseteq>\<^sub>m MT' \<Longrightarrow> rloc_compat MT fd fdf \<Longrightarrow> rloc_compat MT' fd fdf"
    apply (auto simp: rloc_compat_def split: prod.splits option.splits return_loc.split)
    apply force
    apply (simp add: map_leD)
    done

  lemma tm_stack_MT_mono: "MT \<subseteq>\<^sub>m MT' \<Longrightarrow> tm_stack MT stkT stk \<Longrightarrow> tm_stack MT' stkT stk"
    unfolding tm_stack_def
    apply (intro conjI)
    apply (auto 
      simp: tm_frame_def tm_valuation_MT_mono
      elim!: list_all2_mono) []
    apply (auto simp: rloc_compat_mono)
    done

  lemma new_block_spec[e_vcg]:   
    assumes "tm_val MT TInt v"
    assumes "WTv MT \<mu> \<gamma> fd stkT c l stk"
    shows "nte_spec (new_block v \<mu>) (\<lambda>(r,\<mu>'). \<forall>T. \<exists>MT'. 
      MT\<subseteq>\<^sub>mMT' 
    \<and> WTv MT' \<mu>' \<gamma> fd stkT c l stk
    \<and> (tm_val MT' (TPtr T) r))"
    using assms
    apply (cases "(v,\<mu>)" rule: new_block.cases)
    defer
    apply auto []
    apply auto []

    apply clarsimp
    apply (rule exI[where x = "MT(length \<mu> \<mapsto> T)" for T])
    apply (rule context_conjI)
    apply (auto simp: WTv_def tm_def tm_mem_alloc_map_le) []
    apply (auto simp: WTv_def tm_def tm_mem_alloc_pres tm_valuation_MT_mono tm_stack_MT_mono tm_addr_def)
    done


  lemma load_spec[e_vcg]:
    assumes "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_addr MT T addr"
    shows "nte_spec (load addr \<mu>) (\<lambda>v. tm_val MT T v)"
    using assms
    by (fastforce simp: load_def tm_addr_def WTv_def tm_def tm_mem_def valid_mem_def
      split: prod.splits option.splits) 
    
  lemma read_var_spec[e_vcg]:  
    assumes "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "read_varty fd x = Some T"
    shows "nte_spec (read_var x (l,\<gamma>,\<mu>)) (\<lambda>v. tm_val MT T v)"
    using assms
    by (auto split: Error_Monad.bind_splits option.splits simp: read_var_def; (
      (rule read_varty_cases_raw; assumption?; auto)
      )) []


  (* TODO: A more uniform handling of operators would make this proof simpler,
    and, possibly, the semantics cleaner! *)  

  lemmas (in -) e_vcg_val_split[e_vcg] 
    = val.split[where P = "e_spec P E T" for P E T, THEN iffD2, unfolded split_rule_unfolds]  

  lemma eval_WTv_aux:   
    assumes "WTv MT \<mu> \<gamma> fd stkT c l stk" 
    shows "tyeval fd e = Some T \<longrightarrow> nte_spec (eval e (l,\<gamma>,\<mu>)) (\<lambda>(v,(l',\<gamma>',\<mu>')). \<exists>MT'. MT \<subseteq>\<^sub>m MT' \<and> WTv MT' \<mu>' \<gamma>' fd stkT c l' stk \<and> tm_val MT' T v)" (is ?G1)
    and "tyeval_l fd le = Some T \<longrightarrow> nte_spec (eval_l le (l,\<gamma>,\<mu>)) (\<lambda>(addr,(l',\<gamma>',\<mu>')). \<exists>MT'. MT \<subseteq>\<^sub>m MT' \<and> WTv MT' \<mu>' \<gamma>' fd stkT c l' stk \<and> tm_addr MT' T addr)" (is ?G2)
  proof -  
    note [[goals_limit = 3]]
    note [intro] = map_le_trans

    note [simp] = tm_addr_of

    show ?G1 and ?G2
    using assms
    apply (induction e and le arbitrary: l \<gamma> \<mu> MT T and l \<gamma> \<mu> MT T)
    unfolding split_rule_unfolds

    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []

    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []

    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []

    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []

    apply (clarsimp split: Option.bind_splits type.splits split_if_asm; e_vcg) []

    apply (clarsimp split: Option.bind_splits type.splits split_if_asm) []
    apply (e_vcg; (clarsimp;metis map_le_trans))

    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    apply (clarsimp split: Option.bind_splits type.splits; e_vcg) []
    done
  qed  

  lemma eval_spec[e_vcg]: 
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tyeval fd e = Some T"
    shows "nte_spec (eval e (l,\<gamma>,\<mu>)) 
      (\<lambda>(v,(l',\<gamma>',\<mu>')). \<exists>MT'. MT \<subseteq>\<^sub>m MT' \<and> WTv MT' \<mu>' \<gamma>' fd stkT c l' stk \<and> tm_val MT' T v)"  
    using eval_WTv_aux[OF WTv] assms 
    apply (cases "eval e (l,\<gamma>,\<mu>)")
    apply (auto simp: focus_visible_loc_def)
    apply force+
    done


  lemma eval_l_spec[e_vcg]: 
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tyeval_l fd e = Some T"
    shows "nte_spec (eval_l e (l,\<gamma>,\<mu>)) (\<lambda>(addr,(l',\<gamma>',\<mu>')). \<exists>MT'. MT \<subseteq>\<^sub>m MT' \<and> WTv MT' \<mu>' \<gamma>' fd stkT c l' stk \<and> tm_addr MT' T addr)"  
    using eval_WTv_aux[OF WTv] assms 
    apply (cases "eval_l e (l,\<gamma>,\<mu>)")
    apply (auto simp: focus_visible_loc_def)
    apply force+
    done

  lemma tm_valuation_upd: "\<lbrakk> tm_valuation MT Ts vs; tm_val MT T v; Ts x = Some T \<rbrakk> 
    \<Longrightarrow> tm_valuation MT Ts (vs(x \<mapsto> Some v))"  
    unfolding tm_valuation_def
    by auto


  lemma write_var_spec[e_vcg]:  
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "read_varty fd x = Some T"
    assumes "tm_val MT T v"
    shows "nte_spec (write_var x v (l,\<gamma>,\<mu>)) (\<lambda>(l',\<gamma>',\<mu>'). \<mu>'=\<mu> \<and> WTv MT \<mu> \<gamma>' fd stkT c l' stk)"
  proof -
    interpret focus_visible_loc using WTv by unfold_locales

    show ?thesis
      using assms(2,3)  
      apply (auto simp: write_var_def read_varty_def elim: GT_SomeE LT_SomeE split: option.splits)
      apply (rule GT_SomeE, assumption) apply auto []
      unfolding WTv_alt
      apply (auto simp: tm_mem tm_locals tm_globals tm_com tm_slink tm_valuation_upd)
      done
  qed    
    
  lemma (in focus_visible_loc) WT: "WT ((c, l, rloc) # stk, \<gamma>, \<mu>)"  
    using WTv unfolding WT_def WTv_def tm_def by auto
    
  lemma WTv_is_WT: "WTv MT \<mu> \<gamma> fd stkT c l stk \<Longrightarrow> WT ((c, l, rloc) # stk, \<gamma>, \<mu>)"  
    unfolding WT_def WTv_def tm_def by auto

  lemma WTv_upd_com: 
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    shows "tm_com fd c2 \<Longrightarrow> WTv MT \<mu> \<gamma> fd stkT c2 l stk"
    using assms unfolding WTv_alt by auto

  lemma WT_upd_com: 
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    shows "tm_com fd c2 \<Longrightarrow> WT ((c2, l, rloc) # stk, \<gamma>, \<mu>)"
    using WTv unfolding WT_def WTv_def tm_def
    apply (clarsimp)
    apply (rule exI[where x=MT]; simp)
    apply (rule exI[where x="fd#stkT"])
    apply (auto simp: tm_stack_def tm_frame_def)
    done
    
  lemma (in focus_visible_loc) focus_upd_cmd: 
    "tm_com fd c2 \<Longrightarrow> focus_visible_loc p MT \<mu> \<gamma> fd c2 l stkT stk"
    apply unfold_locales
    using assms
    using WTv unfolding WTv_alt by auto


  lemma WT_tr_assign[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_com fd c2"
    assumes "read_varty fd x = Some T"
    assumes "tyeval fd a = Some T"
    shows "nte_spec
            (tr_assign x a
              ((c2, l, rloc) # stk, \<gamma>, \<mu>))
            WT"  
    using assms        
    apply (auto simp: tr_assign_def lift_transformer_nr_def) []
    apply e_vcg
    apply (auto simp: WT_upd_com)
    done

  lemma tm_mem_update:
    assumes "tm_addr MT T (i, j)"
    assumes "tm_val MT T v"
    assumes "valid_mem (i,j) \<mu>"
    assumes "tm_mem MT \<mu>"
    shows "tm_mem MT (\<mu>[i := Some (the (\<mu> ! i)[nat j := Some v])])"
    using assms
    by (fastforce simp: valid_mem_def tm_mem_def tm_addr_def nth_list_update
      split: split_if_asm option.splits)

  lemma WT_store_spec[e_vcg]: 
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_addr MT T addr"
    assumes "tm_val MT T v"
    shows "nte_spec (store addr v (l,\<gamma>,\<mu>)) (\<lambda>(l',\<gamma>',\<mu>'). 
      l'=l \<and> \<gamma>'=\<gamma> \<and> WTv MT \<mu>' \<gamma> fd stkT c l stk)"
    using assms
    apply (auto simp: store_def split: prod.splits option.splits)
    apply unfold_locales unfolding WTv_alt
    apply (auto simp: tm_mem_update)
    done

  lemma WT_tr_assignl[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_com fd c2"
    assumes "tyeval_l fd le = Some T"
    assumes "tyeval fd a = Some T"
    shows "nte_spec
            (tr_assignl le a
              ((c2, l, rloc) # stk, \<gamma>, \<mu>))
            WT"  
  proof - 
    note [simp] = WT_upd_com          
    show ?thesis  
      using assms        
      apply (clarsimp simp: tr_assignl_def lift_transformer_nr_def) []
      apply e_vcg
      done
  qed    

  lemma WT_tr_eval[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_com fd c2"
    assumes "tyeval fd b = Some T"
    shows "nte_spec (tr_eval b ((c2, l, rloc) # stk, \<gamma>, \<mu>)) WT"  
  proof - 
    note [simp] = WT_upd_com          
    show ?thesis  
    using assms
      apply (auto simp: tr_eval_def lift_transformer_nr_def split: prod.splits)
      apply e_vcg
      done
  qed
    
  lemma WT_free_spec[e_vcg]: 
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_addr MT T addr"
    shows "nte_spec (free addr (l,\<gamma>,\<mu>)) (\<lambda>(l',\<gamma>',\<mu>'). 
      l'=l \<and> \<gamma>'=\<gamma> \<and> WTv MT \<mu>' \<gamma> fd stkT c l stk)"
    using assms
    apply (auto simp: free_def split: prod.splits option.splits)
    apply e_vcg
    unfolding WTv_alt
    apply (auto simp: tm_mem_def nth_list_update)
    done

  lemma WT_tr_free[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_com fd c2"
    assumes "tyeval fd e = Some T" "is_TPtr T"
    shows "nte_spec (tr_free e ((c2, l, rloc) # stk, \<gamma>, \<mu>)) WT"  
  proof - 
    note [simp] = WT_upd_com          
    show ?thesis  
      using assms
      apply (cases T; simp)
      apply (auto simp: tr_free_def lift_transformer_nr_def split: prod.splits)
      apply e_vcg
      done
  qed    

  lemma WT_empty: 
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    shows "WT ([],\<gamma>,\<mu>)"
    unfolding WT_def tm_def using assms unfolding WTv_alt 
    by (auto intro!: exI simp: tm_stack_def)

  lemma WT_pop:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes [simp]: "stk = (c',l',rloc')#stk'"  
    obtains fd' stkT' where 
      "stkT = fd'#stkT'" "WTv MT \<mu> \<gamma> fd' stkT' c' l' stk'"
      "rloc_compat MT fd (fd',(c',l',rloc'))"
  proof -
    from WTv have "stkT\<noteq>[]"
      by (auto simp: tm_slink_def WTv_alt)
    then obtain fd' stkT' where [simp]: "stkT = fd'#stkT'" by (cases stkT) auto

    from WTv have "rloc_compat MT fd (fd',(c',l',rloc'))"
      unfolding tm_slink_def WTv_alt
      by auto
    moreover  
    have "WTv MT \<mu> \<gamma> fd' stkT' c' l' stk'"
      using WTv
      unfolding WTv_alt
      apply (auto simp add: tm_slink_def tm_frame_def)
      done
    ultimately show ?thesis   
      by (auto intro: that)
  qed    

  (* TODO: Move *)
  lemmas (in -) e_vcg_rloc_cases[e_vcg] = return_loc.split[where P="e_spec P E T" for P E T, THEN iffD2, unfolded split_rule_unfolds]
  lemmas (in -) e_vcg_list_cases[e_vcg] = list.split[where P="e_spec P E T" for P E T, THEN iffD2, unfolded split_rule_unfolds]

  lemma WT_tr_return[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "RT fd = Some T"
    assumes "tyeval fd e = Some T"
    shows "nte_spec (tr_return e ((c2, l, rloc) # stk, \<gamma>, \<mu>)) WT"
  proof -
    (*note [simp] = WT_pop WT_empty*)
    show ?thesis  
      unfolding tr_return_def
      using assms
      apply (auto simp: lift_transformer_def split: prod.splits)
      apply e_vcg'
      apply (simp add: WT_empty)

      apply (thin_tac "WTv _ _ _ _ _ _ _ _")
      apply (clarsimp simp: lift_transformer_nr_def split: list.splits)
      apply (erule WT_pop, rule refl)
      apply e_vcg
      apply (auto simp add: rloc_compat_def get_rloc_def tm_addr_def RT_def split: option.splits) []
        (* TODO: Too low-level. rloc_compat should use tm_addr! *)

      apply (auto intro: WTv_is_WT) []  

      apply (thin_tac "WTv _ _ _ _ _ _ _ _")
      apply (clarsimp simp: lift_transformer_nr_def split: list.splits)
      apply (erule WT_pop, rule refl)
      apply e_vcg
      apply (auto 
        simp: rloc_compat_def get_rloc_def tm_addr_def RT_def 
        intro: WTv_is_WT
        split: option.splits) [2]

      apply (thin_tac "WTv _ _ _ _ _ _ _ _")
      apply (clarsimp simp: lift_transformer_nr_def neq_Nil_conv split: list.splits)
      apply (erule WT_pop, rule refl)
      apply (auto intro: WTv_is_WT) []  
      done
  qed    

  lemma WT_tr_return_void:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "RT fd = None"
    shows "nte_spec (tr_return_void ((c2, l, rloc) # stk, \<gamma>, \<mu>)) WT"
  proof -
    show ?thesis 
    proof (cases stk)
      case Nil thus ?thesis
      unfolding tr_return_void_def using WTv
      by (auto simp: lift_transformer_def WT_empty split: prod.splits)
    next
      case (Cons fr' stk') then obtain c' l' rloc' where [simp]: "stk = (c',l',rloc')#stk'"
        by (cases fr') auto

      from WT_pop[OF WTv this] obtain fd' stkT' where 
        WTv': "WTv MT \<mu> \<gamma> fd' stkT' c' l' stk'" and
        RLC: "rloc_compat MT fd (fd', c', l', rloc')" .

      (*then interpret fv'!: focus_visible_loc p MT \<mu> \<gamma> fd' c' l' rloc' stkT' stk' by simp*)

      from RLC assms have [simp]: "rloc'=Invalid"
        by (auto simp: RT_def rloc_compat_def split: return_loc.splits option.splits)

      show ?thesis
        using WTv'
        by (auto simp add: tr_return_void_def get_rloc_def intro: WTv_is_WT)
    qed
  qed    

  (*lemma (in focus_visible_loc) set_rloc_spec: 
    "nte_spec (set_rloc rloc' ((c,l,rloc)#stk,\<gamma>,\<mu>)) 
      (\<lambda>(stk',\<gamma>,\<mu>). stk'=(c,l,rloc')#stk \<and> focus_visible_loc p MT \<mu> \<gamma> fd c l stkT stk)"
    unfolding set_rloc_def apply simp
    by unfold_locales*)


  (*TODO: Move *)  
  lemma (in -) o_map_length: "o_map f l = Some l' \<Longrightarrow> length l' = length l"  
    by (induction l arbitrary: l') (auto split: Option.bind_splits)

    
  lemma real_values_spec[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "o_map (tyeval fd) ps = Some Ts"
    shows "nte_spec (real_values ps (l,\<gamma>,\<mu>)) (\<lambda>(vs, (l,\<gamma>,\<mu>)). 
      \<exists>MT'. MT\<subseteq>\<^sub>mMT' \<and> WTv MT' \<mu> \<gamma> fd stkT c l stk \<and> list_all2 (tm_val MT') Ts vs)"
    using assms  
    unfolding real_values_def
    apply (induction ps arbitrary: Ts MT l \<gamma> \<mu>)
    apply auto []
    apply (clarsimp split: Option.bind_splits)
    apply e_vcg' apply (rule refl)
    apply clarsimp
    apply (blast intro: map_le_trans tm_val_MT_mono)
    done

  lemma WTv_push:   
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_frame MT fd' (c',l',rloc')"
    assumes "rloc_compat MT fd' (fd, c, l, rloc)"
    shows "WTv MT \<mu> \<gamma> fd' (fd#stkT) c' l' ((c,l,rloc)#stk)"
    using assms
    unfolding WTv_alt
    apply auto
    unfolding tm_slink_def
    apply (auto simp: tm_frame_def)
    apply (rename_tac i)
    apply (case_tac i; auto)
    apply (rename_tac i)
    apply (case_tac i; auto)
    done

  (* TODO: Move *)  
  lemma (in -) fst_swap_image[simp]: "fst`(\<lambda>(x,y). (y,x))`s = snd`s"
    by force
  lemma (in -) fst_cr_snd_image[simp]: "fst`(\<lambda>x. (f x, g x))`s = f`s"
    by auto    
  lemma (in -) fst_set_zip[simp]: 
    "length l1=length l2 \<Longrightarrow> fst`(set (zip l1 l2)) = (set l1)"  
    apply (induction l1 l2 rule: list_induct2)
    apply auto
    done

  (*lemma map_of_snd_const[simp]: "map_of (map ((\<lambda>x. (x, c)) \<circ> snd) l) 
    = (\<lambda>x. if x\<in>snd`set l then Some c else None)"
    by (induction l) auto*)

  lemma map_of_swap_not_in_dom[simp]: 
    "x\<notin>snd`set l \<Longrightarrow> map_of (map (\<lambda>(x,y). (y,x)) l) x = None"
    by (simp add: map_of_eq_None_iff)  

  lemma tm_valuation_add: "dom v1 \<inter> dom v2 = {} \<Longrightarrow>
    tm_valuation MT T1 v1 \<Longrightarrow> tm_valuation MT T2 v2 \<Longrightarrow> tm_valuation MT (T1++T2) (v1++v2)"  
    unfolding tm_valuation_def
    by (auto simp: dom_def; fastforce)

  lemma typing_of_append[simp]: 
    "snd`set vs1 \<inter> snd`set vs2 = {} \<Longrightarrow> typing_of (vs1@vs2) = typing_of vs1 ++ typing_of vs2"
    unfolding typing_of_def 
    apply (subst map_add_comm)
    apply (auto simp: dom_map_of_conv_image_fst)
    done

  lemma fst_swap_conv[simp]: "(fst \<circ>\<circ> case_prod) (\<lambda>t v. (v, t)) = snd"  
    by auto

  lemma tm_valuation_params:  
    assumes "distinct (map snd ps)"
    assumes "list_all2 (tm_val MT) (map fst ps) pvs"
    shows "tm_valuation MT (typing_of ps) (map_of (zip (map snd ps) (map Some pvs)))"
    using assms
    unfolding tm_valuation_def typing_of_def
    apply (simp add: dom_map_of_conv_image_fst list_all2_iff)
    apply (simp add: zip_map_map zip_map1 zip_map2)
    unfolding in_set_conv_nth Ball_def
    using distinct_idx by (fastforce simp: in_set_conv_nth)

  (* TODO: Move *)  
  lemma init_map_eq_Some_iff[simp]: "init_map D f k = Some v \<longleftrightarrow> k\<in>D \<and> v = f k"
    by (auto simp: init_map_def)
  lemma init_map_eq_None_iff[simp]: "init_map D f k = None \<longleftrightarrow> k\<notin>D"
    by (auto simp: init_map_def)


  lemma tm_valuation_locals:
    assumes "distinct (map snd vdecls)"
    shows "program_loc.tm_valuation MT
         (typing_of (vdecls))
         (init_map (snd ` set (vdecls))
           Map.empty)"
    using assms       
    unfolding tm_valuation_def typing_of_def by fastforce

  lemma mk_locals_spec[e_vcg]:  
    assumes "valid_fun_decl fd"
    assumes "length (fun_decl.params fd) = length pvals"
    assumes "list_all2 (tm_val MT) (map fst (fun_decl.params fd)) pvals"
    shows "nte_spec (mk_locals fd pvals) (\<lambda>l'. tm_valuation MT (LT fd) l')"
    using assms
    unfolding mk_locals_def
    apply (clarsimp simp: LT_def valid_fun_decl_def)
    apply (rule tm_valuation_add)
    apply simp
    apply (simp add: tm_valuation_params)
    apply (simp add: tm_valuation_locals)
    done
    

  lemma init_frame_spec[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "valid_fun_decl fd'"
    assumes "tm_com fd' (fun_decl.body fd')"
    assumes "o_map (tyeval fd) ps = Some (map fst (fun_decl.params fd'))"
    shows "nte_spec (init_frame fd' ps (l,\<gamma>,\<mu>)) (\<lambda>(fr,(l',\<gamma>',\<mu>')). \<exists>MT'. MT\<subseteq>\<^sub>mMT'
      \<and> tm_frame MT' fd' fr 
      \<and> WTv MT' \<mu>' \<gamma>' fd stkT c l' stk)"        
    using assms
    unfolding init_frame_def
    apply -
    apply (frule o_map_length)
    apply (e_vcg dest: list_all2_lengthD simp: tm_frame_def)
    done


  lemma (in well_typed_program) call_function_spec[e_vcg]:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes COMPAT: "rloc_compat MT fd' (fd, c, l, rloc)"
    assumes PT: "proc_table f = Some fd'"
    assumes ARGS_COMPAT: "o2b (args_compat fd fd' ps)"
    shows "nte_spec (call_function proc_table f ps
              ((c, l, rloc) # stk, \<gamma>, \<mu>)) WT"
    using WTv ARGS_COMPAT          
    unfolding call_function_def          
    apply (auto simp: args_compat_def split: Option.bind_splits) []
    apply (frule o_map_length)
    using valid_fun_bodyI[OF PT] valid_fun_declI[OF PT]
    apply (auto simp: lift_transformer_def PT)
    apply e_vcg
    apply (clarsimp simp: push_stack_def)
    apply (erule (1) WTv_is_WT[OF WTv_push])
    using COMPAT apply (auto simp: rloc_compat_def 
      split: return_loc.split option.splits)
    apply (drule (1) map_leD; simp)
    apply (drule (1) map_leD; simp)
    done    

  lemma (in well_typed_program) WT_tr_callfunl:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_com fd c2"
    assumes "o2b (fun_compatl fd le f ps)"
    shows "nte_spec (tr_callfunl proc_table le f ps ((c2, l, rloc) # stk, \<gamma>, \<mu>)) WT"
    using assms
    apply (auto simp: fun_compatl_def tr_callfunl_def lift_transformer_def set_rloc_def
      split: Option.bind_splits)
    apply (e_vcg intro: WTv_upd_com)
    apply (auto simp add: rloc_compat_def tm_addr_def split: option.split)
    done

  lemma (in well_typed_program) WT_tr_callfun:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_com fd c2"
    assumes "o2b (fun_compat fd x f ps)"
    shows "nte_spec (tr_callfun proc_table x f ps ((c2, l, rloc) # stk, \<gamma>, \<mu>)) WT"
    using assms
    apply (auto simp: fun_compat_def tr_callfun_def lift_transformer_def set_rloc_def
      split: Option.bind_splits)
    apply (e_vcg intro: WTv_upd_com)
    apply (auto simp add: rloc_compat_def split: option.split)
    done

  lemma (in well_typed_program) WT_tr_callfunv:
    assumes WTv: "WTv MT \<mu> \<gamma> fd stkT c l stk"
    assumes "tm_com fd c2"
    assumes "o2b (fun_compatv fd f ps)"
    shows "nte_spec (tr_callfunv proc_table f ps ((c2, l, rloc) # stk, \<gamma>, \<mu>)) WT"
    using assms
    apply (auto simp: fun_compatv_def tr_callfunv_def lift_transformer_def set_rloc_def
      split: Option.bind_splits)
    apply (e_vcg intro: WTv_upd_com)
    apply (auto simp add: rloc_compat_def split: option.split)
    done

  lemma (in well_typed_program) WT_step_preserve:
    assumes WT: "WT s"
    assumes S: "s\<rightarrow>sr'"
    shows "nte_spec sr' WT"
    using assms(2,1)
  proof cases
    case (En_fail c1 et en tr c2)
    note [simp] = \<open>sr' = cp_err (en s)\<close>

    from WT \<open>\<not>is_empty_stack s\<close> \<open>c1=com_of s\<close> show ?thesis
    proof (cases rule: focus_visible)
      case (frame stk stkT fd l rloc \<gamma> \<mu> MT)
      note [simp] =frame(1)

      interpret focus_visible_loc p MT \<mu> \<gamma> fd c1 l stkT stk by fact

      from \<open>tm_com fd c1\<close> have "o2b (tycheck_com fd c1)" by simp

      from \<open>cfg c1 (et, en, tr) c2\<close> \<open>o2b (tycheck_com fd c1)\<close> have "nte_spec (en s) (\<lambda>_. True)"
        using WTv
        apply (cases rule: ty_cfg_cases)
        apply (auto simp: simp: en_pos_def en_neg_def lift_transformer_def)
        apply e_vcg+
        done
      thus ?thesis
        using \<open>\<not> Ex (is_res (en s))\<close>
        by (cases "en s") auto

    qed
  next  
    case (Base c1 et en tr c2)
    note [simp] = \<open>sr' = tr (upd_com c2 s)\<close>
    
    from WT \<open>\<not>is_empty_stack s\<close> \<open>c1=com_of s\<close> show ?thesis
    proof (cases rule: focus_visible)
      case (frame stk stkT fd l rloc \<gamma> \<mu> MT)
      note [simp] =frame(1)

      interpret focus_visible_loc p MT \<mu> \<gamma> fd c1 l stkT stk by fact

      from tm_com have tycheck_com1: "o2b (tycheck_com fd c1)" by simp

      from tycheck_com_step1[OF \<open>cfg c1 (et,en, tr) c2\<close>] tm_com have 
        tycheck_com2: "o2b (tycheck_com fd c2)" by simp

      from tycheck_com_step2[OF \<open>cfg c1 (et,en, tr) c2\<close>] tm_com have 
        tm_com2: "et\<noteq>ET_Return \<Longrightarrow> tm_com fd c2" using tycheck_com2 by simp

      from \<open>cfg c1 (et,en, tr) c2\<close> tycheck_com1 show ?thesis
        using WTv
        apply (cases rule: ty_cfg_cases)
        apply (simp_all)
        apply (rule WT_tr_assign; simp add: tm_com2)
        apply (rule WT_tr_assignl; simp add: tm_com2)
        apply (simp add: WT_upd_com tm_com2)
        apply (rule WT_tr_eval; simp add: tm_com2)
        apply (rule WT_tr_eval; simp add: tm_com2)
        apply (rule WT_tr_free; simp add: tm_com2)
        apply (rule WT_tr_return; simp)
        apply (rule WT_tr_return_void; simp)
        apply (rule WT_tr_callfunl; simp add: tm_com2)
        apply (rule WT_tr_callfun; simp add: tm_com2)
        apply (rule WT_tr_callfunv; simp add: tm_com2)
        done
    qed
  next
    case (Return_void )
    note [simp] = \<open>sr' = tr_return_void s\<close>
    
    from WT \<open>\<not>is_empty_stack s\<close> \<open>com_of s = SKIP\<close>[symmetric] show ?thesis
    proof (cases rule: focus_visible)
      case (frame stk stkT fd l rloc \<gamma> \<mu> MT)
      note [simp] =frame(1)

      interpret focus_visible_loc p MT \<mu> \<gamma> fd SKIP l stkT stk by fact

      from tm_com have [simp]: "RT fd = None"
        by simp

      show ?thesis
        using WTv
        apply simp
        apply (erule WT_tr_return_void)
        by simp
    qed
  qed    
        
(*
xxx, ctd here:
  Also include structural errors in nte_spec!
  Show that well-typed program execution does not go wrong!
  Adjust pretty-printer to print typed programs.
*)

    lemma (in well_typed_program) WT_initial: "WT (initial_state)"  
      unfolding WT_def initial_state_def
      apply safe
      apply (rule exI[where x="\<lambda>_. None"])
      apply (rule exI[where x="[main_decl]"])
      unfolding tm_def
    proof safe

      show [simp]: "tm_mem empty initial_mem"
        unfolding tm_mem_def initial_mem_def 
        by auto
      
      show [simp]: "tm_globals empty initial_glob"
        unfolding initial_glob_def tm_valuation_def GT_def typing_of_def
        apply auto
        apply (auto dest!: map_of_SomeD simp: in_set_conv_decomp map_add_Some_iff)
        apply (metis not_None_eq)
        by (metis not_None_eq)

      from main_exists have MP: "proc_table ''main'' = Some main_decl"  
        unfolding proc_table_of_def main_decl_def
        by auto


      from valid_fun_declI[OF MP] have main_valid: "valid_fun_decl main_decl" .
      from valid_fun_bodyI[OF MP] have main_tm: "tm_com main_decl main_com" by (simp add: main_com_def)

      show "tm_stack empty [main_decl] initial_stack"
        unfolding tm_stack_def initial_stack_def
        unfolding tm_frame_def
        apply clarsimp apply safe
        using main_tm
        apply auto [2]
        unfolding tm_valuation_def LT_def typing_of_def main_local_names_def
        apply auto
        apply (auto dest!: map_of_SomeD simp: in_set_conv_decomp map_add_Some_iff)
        apply (metis not_None_eq)
        by (metis not_None_eq)
    qed    


    thm star.induct

    lemma star_induct'[consumes 1, case_names base step]:
      assumes "star R x y"
      assumes "P x"
      assumes "\<And>x y. P x \<Longrightarrow> R x y \<Longrightarrow> P y"
      shows "P y"
      using assms
      apply induction
      apply auto
      done

    lemma (in well_typed_program) yields_no_static_error:
      assumes "yields initial_state cs'"
      shows "nte_spec cs' WT"
      using assms
      unfolding yields_def
    proof safe  
      assume "return initial_state \<rightarrow>* cs'"
      thus "nte_spec cs' (WT)"
        apply (induction rule: star_induct')
        apply (auto simp: WT_initial intro: WT_step_preserve elim!: small_step'.cases)
        done
    qed    

  (* TODO: Move *)  
  lemma pw_eq_return_iff:
    "m = return a \<longleftrightarrow> is_res m a"  
    "return a = m \<longleftrightarrow> is_res m a"  
    by (cases m; auto)+

  lemma is_res_conv: "is_res m x \<longleftrightarrow> m=return x" 
    by (cases m) auto

  (* TODO: Recursion for the error-monad. 
    Then we can argue about partial correctness here, 
    and even relate total correctness to terminates, i.e., show that
    execute terminates iff the program terminates *)
  lemma execute_spec: 
    assumes TERM: "terminates initial_state"
    shows "nte_spec (execute p) (\<lambda>s'. yields initial_state (return s'))"
    unfolding execute_def
  proof e_vcg'
    assume WT: "wt_prog"
    then interpret valid_program p
      unfolding wt_prog_def ..

    from WT interpret well_typed_program p
      unfolding wt_prog_def
      by unfold_locales simp
    
    from interp_correct[OF TERM] 
    have "yields initial_state (interp proc_table initial_state)" 
      by simp
    from yields_no_static_error[OF this] this  
    show "nte_spec 
      (interp proc_table initial_state) 
      (\<lambda>s'. yields initial_state (return s'))"  
      by (auto simp add: pw_espec_iff is_res_conv)
  qed 
end


end
