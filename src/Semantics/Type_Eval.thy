theory Type_Eval
imports Check_Execute "../Typing/Type_Checker" 
begin


  term MT

  context wt_program_loc begin

    definition wt_valuation :: "memory \<Rightarrow> typing \<Rightarrow> valuation \<Rightarrow> bool" where
      "wt_valuation \<mu> ty vs \<equiv> (dom ty = dom vs) 
        \<and> (\<forall>x T addr. ty x = Some T \<and> vs x = Some addr \<longrightarrow> wf_ty SM T \<and> wt_addr \<mu> T addr)"
  
    lemma wt_valuation_empty[simp]: 
      "wt_valuation \<mu> Map.empty vs \<longleftrightarrow> vs=Map.empty"
      "wt_valuation \<mu> tys Map.empty \<longleftrightarrow> tys=Map.empty"
      by (auto simp: wt_valuation_def)



    lemma wt_valuation_add: "
      \<lbrakk>wt_valuation \<mu> T1 v1; wt_valuation \<mu> T2 v2\<rbrakk> 
      \<Longrightarrow> wt_valuation \<mu> (T1++T2) (v1++v2)"
      unfolding wt_valuation_def
      apply clarsimp apply blast done


    context 
      fixes \<mu> :: memory 
      assumes WTM[simp, intro!]: "wt_mem SM \<mu>" 
    begin    

      lemma nsp_wf:
        assumes "norm_struct_ptr \<pi> (lv,ty) = return (lv',ty')"
        assumes "wf_ty SM ty"
        shows "wf_ty SM ty'"
        using assms
        apply (cases "(lv,ty)" rule: norm_struct_ptr.cases)
        apply (auto split: Error_Monad.bind_splits option.splits 
          simp: elookup_def) 
        done

      lemma wf_varty:
        assumes "wf_fun_decl SM fd"
        assumes "varty \<pi> fd x = return T"
        shows "wf_ty SM T"
        using assms WF
        by (auto   
          simp: varty_def elookup_def ET_def wf_fun_decl_def wf_vdecls_def
          simp: wf_program_def Let_def
          dest!: map_of_SomeD
          split: option.splits)

      primrec wf_rty where "wf_rty (_,ty) = wf_ty SM ty" 

      lemma ty_op1_wf:
        assumes "ty_op1 f rty = return rty'"
        assumes "wf_rty rty"
        shows "wf_rty rty'"
        using assms
        apply (cases "(f,rty)" rule: ty_op1.cases)
        apply simp_all
        apply (simp_all split: Error_Monad.bind_splits)
        apply (auto simp: resolve_mname_def elookup_def SM_mt_wf split: option.splits)
        done

      lemma wf_norm_array_ty[simp, intro!]:
        "wf_ty SM ty \<Longrightarrow> wf_ty SM (norm_array_ty ty)"  
        by (cases ty rule: norm_array_ty.cases) auto

      lemma wf_ty_ptr_add:
        "\<lbrakk>ty_ptr_add ty1 ty2 = Some ty'; wf_ty SM ty1; wf_ty SM ty2\<rbrakk> \<Longrightarrow> wf_rty ty'"
        apply (cases "(ty1,ty2)" rule: ty_ptr_add.cases)
        by auto

      lemma wf_ty_arith_binop:
        "\<lbrakk>ty_arith_binop ty1 ty2 = Some ty'; wf_ty SM ty1; wf_ty SM ty2\<rbrakk> \<Longrightarrow> wf_rty ty'"
        apply (cases "(ty1,ty2)" rule: ty_arith_binop.cases)
        by auto

      lemma wf_ty_arith_comp:
        "\<lbrakk>ty_arith_comp ty1 ty2 = Some ty'; wf_ty SM ty1; wf_ty SM ty2\<rbrakk> \<Longrightarrow> wf_rty ty'"
        apply (cases "(ty1,ty2)" rule: ty_arith_comp.cases)
        by auto

      lemma wf_ty_ptr_diff:
        "\<lbrakk>ty_ptr_diff ty1 ty2 = Some ty'; wf_ty SM ty1; wf_ty SM ty2\<rbrakk> \<Longrightarrow> wf_rty ty'"
        apply (cases "(ty1,ty2)" rule: ty_ptr_diff.cases)
        by (auto split: Option.bind_splits)
        
      lemma wf_ty_ptr_comp:
        "\<lbrakk>ty_ptr_comp ty1 ty2 = Some ty'; wf_ty SM ty1; wf_ty SM ty2\<rbrakk> \<Longrightarrow> wf_rty ty'"
        apply (cases "(ty1,ty2)" rule: ty_ptr_comp.cases)
        by (auto split: Option.bind_splits)

      lemma wf_ty_ptr_eq:
        "\<lbrakk>ty_ptr_eq ty1 ty2 = Some ty';wf_ty SM ty1; wf_ty SM ty2\<rbrakk> \<Longrightarrow> wf_rty ty'"
        apply (cases "(ty1,ty2)" rule: ty_ptr_eq.cases)
        by (auto split: Option.bind_splits)

      lemma wf_ty_index:
        "\<lbrakk>ty_index ty1 ty2 = Some ty'; wf_ty SM ty1; wf_ty SM ty2\<rbrakk> \<Longrightarrow> wf_rty ty'"
        apply (cases "(ty1,ty2)" rule: ty_index.cases)
        by (auto split: Option.bind_splits)


      lemma ty_op2_wf:
        assumes "ty_op2 f rty1 rty2 = return rty'"
        assumes "wf_rty rty1"
        assumes "wf_rty rty2"
        shows "wf_rty rty'"
        using assms
        apply (cases f)
        apply (auto 
          simp: ty_op2_def orelse_def 
          dest: wf_ty_ptr_add wf_ty_arith_binop wf_ty_ptr_diff 
          dest: wf_ty_ptr_comp wf_ty_arith_comp wf_ty_ptr_eq wf_ty_index
          split: option.splits prod.splits)
        done

      lemma wf_ty_exp: 
        assumes "ty_exp \<pi> fd e = return rty"
        assumes WFD: "wf_fun_decl SM fd"
        shows "wf_rty rty"
      proof -
        {
          assume "ty_exp_aux \<pi> fd e = return rty" 
          hence "wf_rty rty"
            apply (induction e arbitrary: rty)
            apply (rename_tac f rty) apply (case_tac f)
            apply (auto 
              split: Error_Monad.bind_splits 
              intro: wf_varty[OF WFD]
              elim!: nsp_wf) [3]
            apply (fastforce 
              split: Error_Monad.bind_splits 
              dest: ty_op1_wf elim!: nsp_wf) []
            apply (fastforce 
              split: Error_Monad.bind_splits 
              dest: ty_op2_wf elim!: nsp_wf) []
            done            
        } thus ?thesis  
          using assms
          by (auto simp: ty_exp_def 
              split: error.splits pre_error.splits ck_error.splits option.splits)
      qed  
        
    

      definition "wt_res \<equiv> \<lambda>(lv,T) r. case r of
        res.L addr \<Rightarrow> wt_addr \<mu> T addr \<and> lv
      | res.R v \<Rightarrow> wt_val SM \<mu> T v \<and> \<not>lv \<and> \<not>ty.is_Array T"
    
      lemma wt_res_simps[simp]: 
        "wt_res rty (res.L addr) \<longleftrightarrow> (case rty of (lv,T) \<Rightarrow> wt_addr \<mu> T addr \<and> lv)"
        "wt_res rty (res.R v) \<longleftrightarrow> (case rty of (lv,T) \<Rightarrow> wt_val SM \<mu> T v \<and> \<not>lv \<and> \<not>ty.is_Array T)"
        "wt_res (True,T) r \<longleftrightarrow> (\<exists>addr. r = res.L addr \<and> wt_addr \<mu> T addr)"
        "wt_res (False,T) r \<longleftrightarrow> (\<exists>v. r = res.R v \<and> wt_val SM \<mu> T v \<and> \<not>ty.is_Array T)"
        apply (auto simp: wt_res_def) 
        apply (auto split: res.splits)
        done

      lemma mk_repr_ndspec[e_vcg]: "nd_spec (\<lambda>_. True) (mk_repr i)"
        by (e_vcg simp: mk_repr_def)
  

      lemma to_rval_spec[e_vcg]:
        assumes "wt_res (lv,ty) r"
        assumes "wf_ty SM ty"
        shows "nd_spec (\<lambda>v. wt_val SM \<mu> (norm_array_ty ty) v \<and> v\<noteq>val.Uninit) (to_rval \<mu> r)"
        using assms
        apply (cases r; simp)
        apply (e_vcg' vcg del: cnv_array_to_eptr_spec)
        apply (auto simp: val.is_Array_def wt_val_ty_conv elim!: wt_val.cases) []
        apply e_vcg'
        apply (auto simp: wt_val_ty_conv elim!: wt_val.cases) []
        apply e_vcg'
        apply (auto simp: wt_val_ty_conv elim!: wt_val.cases) []
        done

      lemma to_int_spec[e_vcg]: 
        assumes "wt_res (lv,ty.I) x"
        shows "nd_spec (\<lambda>_. True) (to_int \<mu> x)"
        using assms
        apply (cases x; simp)
        unfolding to_int_def
        apply (e_vcg simp: wt_val_ty_conv)
        apply (e_vcg simp: wt_val_ty_conv)
        done

      lemma un_arith_op_spec[e_vcg]:  
        assumes "wt_res (lv,ty.I) x"
        assumes [e_vcg]: "\<And>i. nd_spec (\<lambda>_. True) (f i)"
        shows "nd_spec (wt_res (False, ty.I)) (un_arith_op \<mu> f x)"
        using assms(1)
        unfolding un_arith_op_def
        apply (e_vcg simp: wt_val_ty_conv)
        done

      lemma to_ptr_spec[e_vcg]:
        assumes "wt_res (lv,T) r"
        assumes "norm_array_ty T = ty.Ptr T'"
        assumes "wf_ty SM T"
        shows "nd_spec (wt_addr \<mu> T') (to_ptr \<mu> r)"
        using assms
        apply (cases T; simp)
        unfolding to_ptr_def

        apply (e_vcg split: val.split  simp: wt_val_ty_conv)
        apply (e_vcg split: val.split  simp: wt_val_ty_conv)
        done        

      lemma nsp_eq:
        assumes "norm_struct_ptr \<pi> (lv,T) = return (lv',T')"
        shows "nty_eq T' T \<and> lv'=lv"
        using assms
        apply (cases "(lv,T)" rule: norm_struct_ptr.cases)
        apply (auto split: Error_Monad.bind_splits)
        done        

      lemma rmn_eq_typing_of[simp]: 
        "resolve_mname sname mts x = return T \<longleftrightarrow> typing_of mts x = Some T"  
        by (auto simp: resolve_mname_def)
        
      lemma wtv_struct_lookupD:
        assumes "typing_of mts name = Some ty"
        assumes "wt_val SM \<mu> (ty.Struct sname mts) (val.Struct ms)"
        shows "\<exists>v. map_of ms name = Some v \<and> wt_val SM \<mu> ty v"
        using assms
        apply (auto simp: wt_val_ty_conv)
        apply fastforce
        done

      lemma memb_op_spec[e_vcg]:
        assumes "wt_res (True,ty.Struct sname mts) v"
        assumes "resolve_mname sname mts name = return ty"
        assumes "wf_ty SM (ty.Struct sname mts)"
        shows "nd_spec (wt_res (True,ty)) (memb_op \<mu> name v)"
        using assms
        apply (cases "(name, v)" rule: memb_op.cases)
        apply (e_vcg)
        apply (e_vcg simp: elookup_def dest!: wtv_struct_lookupD)
        done      

      lemma deref_op_spec[e_vcg]:
        assumes "wt_res (lv,ty.Ptr ty) r"
        assumes "wf_ty SM ty"
        shows "nd_spec (wt_res (True,ty)) (deref_op \<mu> r)"
        using assms
        by (e_vcg simp: deref_op_def)

      lemma membp_op_spec[e_vcg]:
        assumes "wt_res (lv,ty.Ptr (ty.Struct sname mts)) v"
        assumes "resolve_mname sname mts name = return ty"
        assumes "wf_ty SM (ty.Struct sname mts)"
        shows "nd_spec (wt_res (True,ty)) (membp_op \<mu> name v)"
        using assms
        unfolding membp_op_def
        by e_vcg

      lemma wt_res_cong:
        assumes "nty_eq ty ty'"
        assumes [simp]: "wf_ty SM ty" "wf_ty SM ty'"
        shows "wt_res (lv,ty) r \<longleftrightarrow> wt_res (lv,ty') r"
        using assms(1)
        by (fastforce simp: wt_res_def wt_addr_cong wt_val_cong ty.is_Array_def
          split: res.splits)

      lemma nsp_wt_res:
        assumes "norm_struct_ptr \<pi> rty = return rty'"
        assumes WFRTY: "wf_rty rty"
        shows "(wt_res rty r \<longleftrightarrow> wt_res rty' r) \<and> (fst rty'= fst rty) \<and> wf_rty rty'"
      proof -
        obtain lv lv' ty ty' where [simp]:
          "rty = (lv,ty)" "rty' = (lv',ty')"
          by (cases rty; cases rty'; simp)

        from nsp_wf assms have WFRTY': "wf_rty rty'"
          by simp
  
        from nsp_eq[of lv ty lv' ty'] assms(1) have 
          1: "nty_eq ty' ty" and [simp]: "lv'=lv" by auto

        from 1 WFRTY WFRTY' show ?thesis 
          by (auto dest!: wt_res_cong)
      qed    

      lemma ty_ptr_add_conv:
        "ty_ptr_add ty1 ty2 = Some rty \<longleftrightarrow> (\<exists>T. ty1 = ty.Ptr T \<and> ty2 = ty.I \<and> rty = (False,ty.Ptr T))"
        apply (cases "(ty1,ty2)" rule: ty_ptr_add.cases)
        by auto

      lemma ty_arith_binop_conv:
        "ty_arith_binop ty1 ty2 = Some rty \<longleftrightarrow> ty1=ty.I \<and> ty2=ty.I \<and> rty=(False,ty.I)"
        apply (cases "(ty1,ty2)" rule: ty_arith_binop.cases)
        by auto

      lemma ty_arith_comp_conv:
        "ty_arith_comp ty1 ty2 = Some rty \<longleftrightarrow> ty1=ty.I \<and> ty2=ty.I \<and> rty=(False,ty.I)"
        apply (cases "(ty1,ty2)" rule: ty_arith_comp.cases)
        by auto

      lemma ty_ptr_diff_conv: 
        "ty_ptr_diff ty1 ty2 = Some rty \<longleftrightarrow> (\<exists>T. ty1 = ty.Ptr T \<and> ty2 = ty.Ptr T \<and> rty = (False,ty.I))"
        apply (cases "(ty1,ty2)" rule: ty_ptr_diff.cases)
        apply (auto split: Option.bind_splits)
        done  

      lemma ty_ptr_comp_conv: 
        "ty_ptr_comp ty1 ty2 = Some rty \<longleftrightarrow> (\<exists>T. ty1 = ty.Ptr T \<and> ty2 = ty.Ptr T \<and> rty = (False,ty.I))"
        apply (cases "(ty1,ty2)" rule: ty_ptr_comp.cases)
        apply (auto split: Option.bind_splits)
        done  

      lemma ty_ptr_eq_conv: 
        "ty_ptr_eq ty1 ty2 = Some rty \<longleftrightarrow> rty = (False,ty.I) \<and> 
          (
            (\<exists>T. ty1 = ty.Ptr T \<and> ty2 = ty.Ptr T)
          \<or> (\<exists>T. ty1 = ty.Ptr T \<and> ty2 = ty.Null)  
          \<or> (\<exists>T. ty1 = ty.Null \<and> ty2 = ty.Ptr T)
          \<or> (ty1 = ty.Null \<and> ty2 = ty.Null)
          )"
        apply (cases "(ty1,ty2)" rule: ty_ptr_eq.cases)
        apply (auto split: Option.bind_splits)
        done  

      lemma ty_index_conv: 
        "ty_index ty1 ty2 = Some rty \<longleftrightarrow> (\<exists>T. ty1 = ty.Ptr T \<and> ty2 = ty.I \<and> rty = (True,T))"
        apply (cases "(ty1,ty2)" rule: ty_index.cases)
        apply (auto split: Option.bind_splits)
        done  


      lemma norm_array_tyI_conv[simp]:
        "norm_array_ty T = ty.I \<longleftrightarrow> T = ty.I"
        by (cases T) auto

      (*lemma norm_array_ty_conv:
        "norm_array_ty (lv,T) = (lv',ty.Ptr T') \<longleftrightarrow> (lv'=lv \<and> T=ty.Ptr T' \<or> (\<exists>n. lv'=False \<and> T=ty.Array n T'))"
        "\<not>ty.is_Ptr T' \<Longrightarrow> norm_array_ty (lv,T) = (lv',T') \<longleftrightarrow> lv'=lv \<and> T=T' \<and> \<not>ty.is_Array T"
        apply (cases "(lv,T)" rule: norm_array_ty.cases; auto)
        apply (cases T; cases T'; auto)
        done*)

      lemma bin_arith_op_spec[e_vcg]:
        assumes "wt_res (lv1,ty.I) r1"
        assumes "wt_res (lv2,ty.I) r2"
        assumes [e_vcg]: "\<And>i1 i2. nd_spec (\<lambda>_. True) (f i1 i2)"
        shows "nd_spec (wt_res (False,ty.I)) (bin_arith_op \<mu> f r1 r2)"
        using assms(1,2)
        by (e_vcg simp: bin_arith_op_def wt_val_ty_conv)

      lemma eval_exp_spec[e_vcg]:
        assumes WTV: "wt_valuation \<mu> (ET \<pi> fd) EV"
        assumes WTF: "wf_fun_decl SM fd"
        assumes TE: "ty_exp \<pi> fd e = return rty"
        shows "nd_spec (\<lambda>r. wt_res rty r) (eval_exp EV \<mu> e)"
        using TE
      proof (induction e arbitrary: rty)
        case (E0 f)
  
        show ?case proof (cases f)
          case [simp]: (Const i)
          with E0 have [simp]: "rty = (False,ty.I)"
            by (auto simp: ty_exp_def
              split: error.splits pre_error.splits 
                Error_Monad.bind_split_asm ck_error.splits prod.splits option.splits)
  
          show ?thesis
            by (e_vcg intro: wt_val.intros)
        next
          case [simp]: (Null)
          from E0 have [simp]: "rty = (False,ty.Null)"
            by (auto simp: ty_exp_def
              split: error.splits pre_error.splits 
                Error_Monad.bind_split_asm ck_error.splits prod.splits option.splits)
  
          show ?thesis  
            by (e_vcg intro: wt_val.intros)
        next
          case [simp]: (Var x)
  
          from E0 obtain Th T lv where
            VT: "varty \<pi> fd x = return Th"
            and NSP: "norm_struct_ptr \<pi> (True,Th) = return (lv,T)"
            and [simp]: "rty = (lv,T)"
            by (auto simp: ty_exp_def
                norm_struct_ptr_pres_lv[where lv=True]
              split: error.splits pre_error.splits 
                Error_Monad.bind_split_asm ck_error.splits prod.splits option.splits)
          hence [simp]: "lv = True" by (blast dest: norm_struct_ptr_pres_lv)  
  
          from VT have [simp]: "ET \<pi> fd x = Some Th"
            by (auto simp: varty_def)
  
          from WTV obtain addr where 
            [simp]: "EV x = Some addr"
            and WFTH[simp]: "wf_ty SM Th"
            and WTH: "wt_addr \<mu> Th addr"
            apply (auto simp: wt_valuation_def dom_def) apply fastforce
            done
            
          from NSP have EQ: "nty_eq T Th"
            apply (cases "((True,Th))" rule: norm_struct_ptr.cases)
            apply (auto split: Error_Monad.bind_splits)
            done

          from nsp_wf[OF NSP] have WFT: "wf_ty SM T" by simp 

          show ?thesis using WTH wt_addr_cong[OF EQ WFT WFTH]
            by (cases addr) auto
        qed
      next
        case (E1 f e)
        
        from E1.prems obtain rtya rtyb where
          TA: "ty_exp \<pi> fd e = return rtya" 
          and TB: "ty_op1 f rtya = return rtyb"
          and T: "norm_struct_ptr \<pi> rtyb = return rty"
          by (auto 
            simp: ty_exp_def
            split: Error_Monad.bind_splits ck_error.splits option.splits
            split: error.splits pre_error.splits)

        from E1.IH[OF TA] have [e_vcg]: "nd_spec (wt_res rtya) (eval_exp EV \<mu> e)" .  

        from wf_ty_exp[OF TA WTF] have "wf_rty rtya" by simp
        from wf_ty_exp[OF E1.prems WTF] have "wf_rty rty" .

        show ?case
          using TB T
          apply (cases "(f,rtya)" rule: ty_op1.cases)
          apply clarsimp_all
          apply (e_vcg simp: iop_uminus_def)
          apply (e_vcg simp: iop_Not_def)
          apply (e_vcg simp: iop_BNot_def)
          using \<open>wf_rty rtya\<close> \<open>wf_rty rty\<close>
          apply (e_vcg dest: nsp_wt_res)

          apply (e_vcg split: Error_Monad.bind_split_asm simp: wt_val_ty_conv)
            
          using \<open>wf_rty rtya\<close> \<open>wf_rty rty\<close>  
          apply (e_vcg 
            split: Error_Monad.bind_split_asm
            dest!: nsp_eq SM_mt_wf wt_addr_cong
            )

          using \<open>wf_rty rtya\<close>  
          apply (e_vcg 
            split: Error_Monad.bind_split_asm
            dest!: nsp_wt_res simp: SM_mt_wf
            )
          done
      next
        case (E2 f e1 e2)

        from E2.prems obtain rty1a rty2a rtyb where
          TA: "ty_exp \<pi> fd e1 = return rty1a" "ty_exp \<pi> fd e2 = return rty2a"
          and TB: "ty_op2 f rty1a rty2a = return rtyb"
          and T: "norm_struct_ptr \<pi> rtyb = return rty"
          by (auto 
            simp: ty_exp_def
            split: Error_Monad.bind_splits ck_error.splits option.splits
            split: error.splits pre_error.splits)

        from E2.IH(1)[OF TA(1)] have 
          [e_vcg]: "nd_spec (wt_res rty1a) (eval_exp EV \<mu> e1)" .  
        from E2.IH(2)[OF TA(2)] have 
          [e_vcg]: "nd_spec (wt_res rty2a) (eval_exp EV \<mu> e2)" .  

        from wf_ty_exp[OF TA(1) WTF] wf_ty_exp[OF TA(2) WTF] have 
          WFA: "wf_rty rty1a" "wf_rty rty2a" 
          by simp_all

        from ty_op2_wf[OF TB] WFA have WFB: "wf_rty rtyb" by simp  

        from wf_ty_exp[OF E2.prems WTF] have WFT: "wf_rty rty" .

        have "nd_spec (wt_res rtyb) (eval_exp EV \<mu> (exp.E2 f e1 e2))"
          using TB
          apply (cases rty1a; cases rty2a; simp)
          apply (cases f; simp_all add: ty_op2_def split: option.splits)
          apply (clarsimp_all 
              simp: orelse_def rvop2_def[abs_def] 
              simp: ty_arith_binop_conv ty_ptr_add_conv ty_ptr_diff_conv 
                ty_ptr_comp_conv ty_arith_comp_conv ty_ptr_eq_conv ty_index_conv
              split: option.splits)
          
          using WFA
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv)
          apply safe []
          apply (e_vcg' simp: wt_val_ty_conv)
          apply (e_vcg simp: wt_val_ty_conv dest: wf_norm_array_ty)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_plus_def)

          using WFA
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv)
          apply (clarsimp simp: wt_val_ty_conv)
          apply (safe; simp) []
          apply (e_vcg dest: wf_norm_array_ty simp: wt_val_ty_conv)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_minus_def)
          
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_mult_def)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_div_def)
          
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_mod_def)

          using WFA
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv)
          apply (clarsimp simp: wt_val_ty_conv)
          apply (safe; simp add: wt_val_ty_conv) []
          apply (e_vcg simp: wt_val_ty_conv
            simp: addr_less_def split: ptr_comp_res.split)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_less_def)

          using WFA
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv)
          apply (clarsimp simp: wt_val_ty_conv)
          apply (safe; simp add: wt_val_ty_conv) []
          apply (e_vcg simp: wt_val_ty_conv
            simp: addr_leq_def split: ptr_comp_res.split)
          
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_le_def)

          using WFA
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv)
          apply (safe; clarsimp simp: wt_val_ty_conv; safe; simp add: wt_val_ty_conv)
          apply (e_vcg simp: wt_val_ty_conv
            simp: addr_eq_def split: ptr_comp_res.split)
          
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_eq_def)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_And_def)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_Or_def)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_BAnd_def)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_BOr_def)

          apply (e_vcg' simp: rvop2_def wt_val_ty_conv iop_BXor_def)

          using WFA
          apply (e_vcg' simp: rvop2_def wt_val_ty_conv index_op_def)
          apply (safe; clarsimp simp: wt_val_ty_conv)
          apply (e_vcg simp: wt_val_ty_conv)
          done
        also have "wt_res rtyb = wt_res rty"
          using nsp_wt_res[OF T \<open>wf_rty rtyb\<close>] by auto
        finally show ?case by simp 
      qed  
    end

    typ state

    definition wt_raddr :: "memory \<Rightarrow> ty option \<Rightarrow> addr option \<Rightarrow> bool" where
      "wt_raddr \<mu> ty addr \<equiv> case (ty,addr) of
        (Some ty, Some addr) \<Rightarrow> wt_addr \<mu> ty addr
      | (_, None) \<Rightarrow> True
      | _ \<Rightarrow> False"

    lemma wt_raddr_Some[simp]: "wt_raddr \<mu> (Some ty) (Some addr) \<longleftrightarrow> wt_addr \<mu> ty addr" 
      by (auto simp: wt_raddr_def split: option.split)
      
    lemma wt_raddr_None[simp]: "wt_raddr \<mu> x None"
      by (auto simp: wt_raddr_def split: option.split)

    lemma wt_raddr_mono: 
      assumes "wt_raddr \<mu> rt ra"
      assumes "\<mu> \<subseteq>\<^sub>\<mu> \<mu>'"
      shows "wt_raddr \<mu>' rt ra"
      using assms wt_addr_mono
      by (auto simp: wt_raddr_def split: option.splits)


    definition wt_stack_frame :: "memory \<Rightarrow> stack_frame \<Rightarrow> bool" where
      "wt_stack_frame \<mu> \<equiv> \<lambda>(fd,c,l,r). 
        fd \<in> set (program.functs \<pi>)
      \<and> wf_com SM c
      \<and> ty_com \<pi> fd c = return () 
      \<and> wt_valuation \<mu> (typing_of (fun_decl.params fd @ fun_decl.locals fd)) l
      \<and> wt_raddr \<mu> (fun_decl.rtype fd) r
      "

    definition wt_state :: "state \<Rightarrow> bool" where
      "wt_state \<equiv> \<lambda>(\<sigma>,\<gamma>,\<mu>). 
        wt_mem SM \<mu> 
      \<and> wt_valuation \<mu> (typing_of (program.globals \<pi>)) \<gamma>
      \<and> (\<forall>fr\<in>set \<sigma>. wt_stack_frame \<mu> fr)"

    lemma cfg_pres_wfcom:  
      assumes "cfg c e c'"
      assumes "wf_com SM c"
      shows "wf_com SM c'"
      using assms
      apply induction
      apply (auto)
      done

    lemma cfg_pres_tycom1:
      assumes "cfg c e c'"
      assumes "ty_com1 \<pi> fd c = return ()"
      shows "ty_com1 \<pi> fd c' = return ()"
      using assms
      apply induction
      apply (auto split: Error_Monad.bind_splits)
      done

    lemma cfg_pres_tycom2:
      assumes "cfg c e c'"
      assumes "ty_com2 fd c"
      assumes "e \<noteq> label.Effect (effect.Func fcom.Returnv)"
      assumes "\<forall>x. e \<noteq> label.Effect (effect.Func (fcom.Return x))"
      shows "ty_com2 fd c'"
      using assms
      apply induction
      apply (clarsimp_all simp: ty_com_def split: Error_Monad.bind_splits)
      apply (rename_tac c; case_tac c; simp)
      apply (rename_tac c; case_tac c; auto)
      done

    lemma cfg_pres_tycom:  
      assumes C: "cfg c e c'"
      assumes TC: "ty_com \<pi> fd c = return ()"
      assumes NRV: "e \<noteq> label.Effect (effect.Func fcom.Returnv)"
      assumes NR: "\<forall>x. e \<noteq> label.Effect (effect.Func (fcom.Return x))"
      shows "ty_com \<pi> fd c' = return ()"
      using cfg_pres_tycom1[OF C, of fd] cfg_pres_tycom2[OF C _ NRV NR, of fd] TC
      by (auto simp: ty_com_def split: Error_Monad.bind_splits)


    lemma ty_cfg_cases[consumes 3, case_names assign malloc free return returnv callfun callfunv pos neg]:
      assumes "cfg c e c'"
      assumes "wf_com SM c"
      assumes "ty_com \<pi> fd c = return ()"
      obtains 
        e1 e2 T1 T2 where "e = label.Effect (effect.Basic (bcom.Assign e1 e2))"
          "ty_exp \<pi> fd e1 = return T1" "ty_exp \<pi> fd e2 = return T2"
          "ty_assign T1 T2 = return ()"
      | e1 T e2 T1 where "e = label.Effect (effect.Basic (bcom.Malloc e1 T e2))"
          "ty_exp \<pi> fd e1 = return T1" "assert_int_exp \<pi> fd e2 = return ()"
          "ty_assign T1 (False,ty.Ptr T) = return ()" "wf_ty SM T"
      | e1 lv1 T1' where "e = label.Effect (effect.Basic (bcom.Free e1))"  
          "ty_exp \<pi> fd e1 = return (lv1,T1')" "ty.is_Ptr (norm_array_ty T1')"
      | e1 lv1 T1' where "e = label.Effect (effect.Func (fcom.Return e1))"    
          "ty_exp \<pi> fd e1 = return (lv1,T1')" "RT fd = Some (norm_array_ty T1')"
      | "e = label.Effect (effect.Func (fcom.Returnv))"    
          "RT fd = None"
      | e1 name args where "e = label.Effect (effect.Func (fcom.Callfun e1 name args))"
          "fun_compat \<pi> fd e1 name args = return ()"
      | name args where "e = label.Effect (effect.Func (fcom.Callfunv name args))"
          "fun_compatv \<pi> fd name args = return ()"
      | "e = label.Effect effect.Skip"    
      | e1 where "e = label.Guard (guard.Pos e1)" "assert_int_ptr_exp \<pi> fd e1 = return ()"
      | e1 where "e = label.Guard (guard.Neg e1)" "assert_int_ptr_exp \<pi> fd e1 = return ()"
    proof -
      from assms(3) have "ty_com1 \<pi> fd c = return ()"
        by (auto simp: ty_com_def split: Error_Monad.bind_splits)
      with assms(1,2) that show ?thesis  
        apply (induction)
        apply (simp_all)
        apply (rename_tac c)
        apply (case_tac c; auto split: Error_Monad.bind_splits simp: Let_def)
        apply (rename_tac c)
        apply (case_tac c; auto split: Error_Monad.bind_splits simp: Let_def)
        apply (auto split: Error_Monad.bind_splits) []
        apply (auto split: Error_Monad.bind_splits) []
        apply (auto split: Error_Monad.bind_splits) []
        done
    qed    
      

    lemmas edge_split_e_vcg[e_vcg] = edge.split[where P="e_spec P E T" for P E T, THEN iffD2, unfolded split_rule_unfolds]
  
    lemma efold_invar:
      assumes "I s"
      assumes "\<And>x s. \<lbrakk>x\<in>set l; I s\<rbrakk> \<Longrightarrow> nd_spec I (f x s)"
      shows "nd_spec I (efold f l s)"
      using assms
      apply (induction l arbitrary: s)
      apply e_vcg+
      done


    lemma destroy_frame_spec[e_vcg]: 
      "\<lbrakk>wt_mem SM \<mu>\<rbrakk> \<Longrightarrow> nd_spec (\<lambda>\<mu>'. wt_mem SM \<mu>' \<and> \<mu> \<subseteq>\<^sub>\<mu> \<mu>') (destroy_frame fr \<mu>)"
      unfolding destroy_frame_def
      apply (clarsimp split: prod.split)
      apply (e_vcg vcg: efold_invar intro: mem_ord_trans)
      done

    lemma wt_valuation_mono:
      assumes "wt_valuation \<mu> ty vs"
      assumes "\<mu> \<subseteq>\<^sub>\<mu> \<mu>'"
      shows "wt_valuation \<mu>' ty vs"
      using assms(1)
      using wt_addr_mono[OF _ assms(2)]
      by (auto simp: wt_valuation_def)

    lemma wt_stack_frame_mono:
      assumes "wt_stack_frame \<mu> fr"
      assumes M: "\<mu> \<subseteq>\<^sub>\<mu> \<mu>'"
      shows "wt_stack_frame \<mu>' fr"
      using assms(2,1)
      by (auto 
        simp: wt_stack_frame_def 
          wt_valuation_mono[OF _ M] wt_addr_mono[OF _ M] wt_raddr_def 
        split: option.splits)

    lemma wt_stack_frames_mono:
      assumes "\<forall>fr\<in>set stk. wt_stack_frame \<mu> fr"
      assumes "\<mu> \<subseteq>\<^sub>\<mu> \<mu>'"
      shows "\<forall>fr\<in>set stk. wt_stack_frame \<mu>' fr"
      using assms wt_stack_frame_mono by auto

    (* TODO/FIXME: Ad-Hoc hack to transfer heap properties! *)  
    lemmas mo_monos = wt_addr_mono wt_raddr_mono wt_stack_frame_mono wt_val_mono
      wt_valuation_mono wt_stack_frames_mono

    lemmas tagged_monos = mo_monos[THEN ID_TAGI]


    lemma eval_args_spec[e_vcg]:
      assumes WTM[simp]: "wt_mem SM \<mu>"
      assumes WTV: "wt_valuation \<mu> (ET \<pi> fd) ev"
      assumes WTF: "wf_fun_decl SM fd"
      assumes ARGS: "emap (ty_exp \<pi> fd) args = return Ts"
      shows "nd_spec (\<lambda>vs. list_all2 (wt_val SM \<mu>) (map (norm_array_ty o snd) Ts) vs) (eval_args args ev \<mu>)"
      using ARGS unfolding eval_args_def
      apply (induction args arbitrary: Ts)
      apply e_vcg'
      using WTV WTF
      apply (e_vcg split: Error_Monad.bind_split_asm 
        dest: wf_ty_exp[OF WTM _ WTF] 
        simp: wf_rty.simps[OF WTM])
      done

    lemma return_ty_assignD:
      assumes TYA: "ty_assign' T' T = return ()"
      assumes FEX: "mk_fun_map \<pi> name = Some fdn"
      assumes RTY: "fun_decl.rtype fdn = Some T"
      shows "T'=T"
    proof -
      from FEX have "ty_fdecl \<pi> fdn = return ()" using WT
        unfolding wt_program_def ty_program_def
        apply (auto simp: Let_def wf_fun_decls_def mk_fun_map_def in_set_conv_decomp
          dest!: map_of_SomeD
          )
        apply (cases "ty_fdecl \<pi> fdn")
        apply (auto split: ck_error.splits option.splits)
        done

      with RTY have "\<not>ty.is_Array T \<and> T\<noteq>ty.Null" 
        apply (cases T)
        apply (auto simp: ty_fdecl_def RT_def split: Error_Monad.bind_splits option.splits)
        done
      with TYA show ?thesis  
        apply (cases T)
        apply (auto simp: ty_assign'_def Let_def)
        done
    qed    

    lemma wt_valuation_upd:
      assumes "wt_valuation \<mu> tys vs"
      assumes "wt_addr \<mu> ty v"
      assumes "wf_ty SM ty"
      shows "wt_valuation \<mu> (tys(name\<mapsto>ty)) (vs(name\<mapsto>v))"
      using assms
      unfolding wt_valuation_def
      by auto

    (*
      map with state:
        f :: x \<Rightarrow> s \<Rightarrow> (y,s)
        l :: x list
        s0 :: s

      \<rightarrow> efold (\<lambda>x (l,s). do { (y,s) \<leftarrow> f x s; return (y#l, s) })  

    definition emap_st :: "('a \<Rightarrow> 's \<Rightarrow> ('b\<times>'s,'e) error) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> (('b list\<times>'s),'e) error"
    where "emap_st f l s0 \<equiv> do {
      efold (\<lambda>a (l,s). do { (b,s) \<leftarrow> f a s; return (b#l,s) }) l ([],s0)
    }"

    lemma
      fixes f
      defines "emf \<equiv> \<lambda>a (l,s). do { (b,s) \<leftarrow> f a s; return (b#l,s) }"
      shows "efold emf l (l0,s0) = do { (l',s) \<leftarrow> efold emf l ([],s0); return (l'@l0,s) }"
    proof -
      have U: "\<And>l. efold emf l = (\<lambda>(l',s). efold emf l (l',s))" by auto
      show ?thesis
      proof (induction l arbitrary: l0 s0)
        case (Cons a l)
        show ?case
          apply simp
          apply (subst U)
          apply (subst Cons.IH)
          apply simp

        apply simp
        apply simp
        apply (subst U)
        apply 

    lemma emap_st_simps:
      "emap_st f [] s0 = return ([],s0)"
      "emap_st f (a#l) s = do { (b,s) \<leftarrow> f a s; (l',s) \<leftarrow> emap_st f l s; return (b#l',s)}"
      apply (auto simp: emap_st_def split: prod.splits Error_Monad.bind_splits)
      

    lemma emap_st_rule:
      assumes INV0: "st_inv s"
      assumes STEP: "\<And>a s. \<lbrakk> st_inv s; a\<in>set l \<rbrakk> \<Longrightarrow> e_spec (\<lambda>(b,s'). st_inv s' \<and> link_prop a b) E T (f a s)"
      shows "e_spec (\<lambda>(l',s'). list_all2 (link_prop) l l') E T (emap_st f l s)"
      using INV0
      apply (induction l arbitrary: s)
      apply (simp add: emap_st_def)

    *)  



    lemma alloc_params_spec[e_vcg]:
      fixes decls :: "(char list \<times> ty) list" and vals :: "val list"
      assumes VALS_VALID: "list_all2 (wt_val SM \<mu>) (map snd decls) vals"
      assumes "wt_mem SM \<mu>"
      assumes WF_VDECLS: "wf_vdecls SM decls"
      shows "nd_spec (\<lambda>(vs,\<mu>'). \<mu>\<subseteq>\<^sub>\<mu>\<mu>' \<and> wt_mem SM \<mu>' \<and> wt_valuation \<mu>' (typing_of decls) vs) (alloc_params decls vals \<mu>)"
      apply (simp add: alloc_params_def)
      apply e_vcg'
    proof -
      case goal1
      assume LEN_EQ: "length decls = length vals"
      let "nd_spec ?P (efold ?f _ _)" = ?case

      def TAG\<equiv>"\<lambda>x::bool. x"

      {
        fix \<mu>0 vs0 ts0
        assume "\<mu> \<subseteq>\<^sub>\<mu> \<mu>0"
        and "wt_mem SM \<mu>0"
        and "wt_valuation \<mu>0 ts0 vs0"
        and "TAG (dom ts0 \<inter> (dom (typing_of decls)) = {})"
        with LEN_EQ VALS_VALID WF_VDECLS have "nd_spec 
          ((\<lambda>(vs,\<mu>'). \<mu>0\<subseteq>\<^sub>\<mu>\<mu>' \<and> wt_mem SM \<mu>' \<and> wt_valuation \<mu>' (ts0 ++ typing_of decls) (vs))) 
          (efold ?f (zip decls vals) (vs0,\<mu>0))"
          apply (induction arbitrary: vs0 \<mu>0 ts0 rule: list_induct2)
          apply simp
          apply (e_vcg' 
            simp: wt_val_mono wf_vdecls_def nonzero_tyI[OF WF]
            simp: valid_decls_def
            elim!: mem_ord_trans
            )
          apply (drule wt_valuation_mono, assumption)
          apply (rule wt_valuation_upd; assumption)

          apply (auto simp: TAG_def) []
          apply (auto elim: mem_ord_trans 
            simp: TAG_def dom_map_of_conv_image_fst)
          done
      } note GEN = this

      from GEN[OF mem_ord_refl \<open>wt_mem SM \<mu>\<close>, of Map.empty Map.empty]
        show ?case
        by (auto simp: TAG_def)
    next
      case goal2 with list_all2_lengthD[OF VALS_VALID] have False by simp
      thus ?case ..
    qed    

    lemma alloc_vdecls_spec[e_vcg]:
      fixes decls :: "(char list \<times> ty) list" and vals :: "val list"
      assumes WTM: "wt_mem SM \<mu>"
      assumes WF_VDECLS: "wf_vdecls SM decls"
      shows "nd_spec (\<lambda>(vs,\<mu>'). 
          \<mu>\<subseteq>\<^sub>\<mu>\<mu>' 
        \<and> wt_mem SM \<mu>' 
        \<and> wt_valuation \<mu>' (typing_of decls) vs) 
      (alloc_vdecls decls \<mu>)"
      apply (simp add: alloc_vdecls_def)
    proof -
      case goal1
      let "nd_spec _ (efold ?f _ _)" = ?case
  
      def TAG\<equiv>"\<lambda>x::bool. x"

      {
        fix vs0 ts0
        assume "wt_valuation \<mu> ts0 vs0"
        and "wt_mem SM \<mu>"
        and "wf_vdecls SM decls"
        and "TAG (dom ts0 \<inter> dom (typing_of decls) = {})"
        hence "nd_spec (\<lambda>(vs, \<mu>').
            \<mu> \<subseteq>\<^sub>\<mu> \<mu>' 
          \<and> wt_mem SM \<mu>' 
          \<and> wt_valuation \<mu>' (ts0 ++ typing_of decls) vs)
          (efold ?f decls (vs0,\<mu>))"
          apply (induction decls arbitrary: vs0 ts0 \<mu>)
          apply simp
          apply (e_vcg' simp: nonzero_tyI[OF WF])
          apply (drule wt_valuation_mono, assumption)
          apply (rule wt_valuation_upd; assumption)

          apply (auto simp: TAG_def) []
          apply (auto elim: mem_ord_trans dest: map_of_SomeD 
            simp: TAG_def dom_map_of_conv_image_fst)
          done 
      } note aux=this
      
      from aux[of Map.empty Map.empty, OF _ WTM WF_VDECLS] show ?case
        by (auto simp: TAG_def)
    qed   


    lemma rp_ty_imp_nty_eq: "\<lbrakk>valid_rp_type ty\<rbrakk> \<Longrightarrow> norm_array_ty ty = ty"
      by (cases ty) auto

    lemma map_nty_param_eq:
      assumes FD: "mk_fun_map \<pi> name = Some fdn"  
      shows "map (norm_array_ty \<circ> snd) (fun_decl.params fdn) = map snd (fun_decl.params fdn)"
    proof -
      have VR: "\<forall>ty\<in>set (map snd (fun_decl.params fdn)). valid_rp_type ty"
        using ty_fdeclI[OF assms]
        by (auto simp: ty_fdecl_def split: Error_Monad.bind_splits)
      {
        fix l
        assume "\<forall>ty\<in>set l. valid_rp_type ty"
        hence "map norm_array_ty l = l"
          by (induction l) (auto simp: rp_ty_imp_nty_eq)
      } 
      from this[OF VR] show ?thesis by auto 
    qed  


    lemma op_call_spec[e_vcg]: 
      assumes FD: "mk_fun_map \<pi> name = Some fdn"
      assumes PT: "list_all2 (wt_val SM \<mu>) (map (norm_array_ty \<circ> snd) (fun_decl.params fdn)) argvs"
      assumes RA: "\<And>addr. rtv = Some addr \<Longrightarrow> \<exists>T. fun_decl.rtype fdn = Some T \<and> wt_addr \<mu> T addr"
      assumes WTS: "wt_state (\<sigma>,\<gamma>,\<mu>)"
      shows "nd_spec wt_state (op_call rtv fdn argvs (\<sigma>,\<gamma>,\<mu>))"
    proof -
      from FD have FDIF[simp]: "fdn \<in> set (program.functs \<pi>)"
        by (auto simp: mk_fun_map_def dest: map_of_SomeD)

      from wf_fdeclI[OF FD] have WFFD: "wf_fun_decl SM fdn" .
      hence 
        aux1: "wf_vdecls SM (fun_decl.params fdn)"
        and aux2: "wf_vdecls SM (fun_decl.locals fdn)"
        and aux3: "
          dom (typing_of (fun_decl.params fdn)) 
        \<inter> dom (typing_of (fun_decl.locals fdn)) = {}"
        by (auto simp: wf_fun_decl_def dest: map_of_SomeD)
        

      from WFFD have [simp]: "wf_com SM (fun_decl.body fdn)"    
        by (auto simp: wf_fun_decl_def)

      from ty_fdeclI[OF FD] have 
        [simp]: "ty_com \<pi> fdn (fun_decl.body fdn) = return ()"
        by (auto simp: ty_fdecl_def split: Error_Monad.bind_splits)


      show ?thesis
        unfolding op_call_def create_frame_def
        using PT WTS FD aux1 aux2
        apply (e_vcg' simp: wt_state_def map_nty_param_eq)
        apply clarsimp
        apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)+
        apply (auto 
          simp: wt_stack_frame_def map_add_comm[OF aux3, symmetric]
          simp: wt_valuation_add
          ) []
        apply (cases rtv; simp) apply auto []
        apply (drule RA)
        apply clarsimp
        apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)+
        apply auto
        done
    qed    

    lemma ty_assign'_wtD:
      assumes "ty_assign' ty1 ty2 = return ()"
      assumes "wt_val SM \<mu> (norm_array_ty ty2) x"
      shows "wt_val SM \<mu> ty1 x"
      using assms unfolding ty_assign'_def
      by (auto simp: Let_def wt_val_ty_conv is_Ptr_def)

    lemma ss_step_spec[e_vcg]:
      assumes NE: "\<not>is_empty_stack s"
      assumes WT: "wt_state s"
      shows "nd_spec (wt_state) (ss_step \<pi> s)"
    proof -  
      from NE obtain fd c l rt \<sigma>' \<gamma> \<mu> where [simp]: "s = ((fd,c,l,rt)#\<sigma>',\<gamma>,\<mu>)"
        by (cases s) (auto simp: neq_Nil_conv)

      from WT have 
        WTM[simp]: "wt_mem SM \<mu>"  
        and WTG: "wt_valuation \<mu> (typing_of (program.globals \<pi>)) \<gamma>"
        and WT_TOP_FR: "wt_stack_frame \<mu> (fd,c,l,rt)"
        and WTFRS: "(\<forall>fr\<in>set \<sigma>'. wt_stack_frame \<mu> fr)"
        by (auto simp: wt_state_def)

      from WT_TOP_FR have  
        FD: "fd \<in> set (program.functs \<pi>)"
        and WFC: "wf_com SM c"
        and TYC: "ty_com \<pi> fd c = return ()"
        and WTL: "wt_valuation \<mu> (typing_of (fun_decl.params fd @ fun_decl.locals fd)) l"
        and WTRA: "wt_raddr \<mu> (fun_decl.rtype fd) rt"
        by (auto simp: wt_stack_frame_def)

      from WTL WTG
      have WTV: "wt_valuation \<mu> (ET \<pi> fd) (\<gamma> ++ l)"  
        apply (auto simp: ET_def)
        apply (metis wt_valuation_add map_add_assoc)
        done

      from FD WF have WFFD[simp]: "wf_fun_decl SM fd"
        unfolding wf_program_def
        by (auto simp: Let_def wf_fun_decls_def)
        
      from WFFD have WFRT[simp]: "\<And>T. RT fd = Some T \<Longrightarrow> wf_ty SM T" 
        unfolding wf_fun_decl_def RT_def by auto

      {
        fix c'
        assume "rt=None"
        hence "nd_spec wt_state
          (op_return None ((fd, c', l, rt) # \<sigma>', \<gamma>, \<mu>))"
          using WTG WTFRS
          by (e_vcg 
            simp: op_return_def assign_return_value_def wt_state_def
            intro: wt_valuation_mono wt_stack_frame_mono)
      } note aux_returnv0 = this

      {
        assume "c = com.Skip"
        hence "rt=None" using TYC WTRA
          by (auto simp: ty_com_def wt_raddr_def RT_def split: option.splits)
        note aux_returnv0[OF this]  
      } note aux_return_skip = this

      {
        fix c'
        assume "RT fd = None"
        hence "rt = None" using WT_TOP_FR
          by (auto simp: wt_stack_frame_def RT_def wt_raddr_def split: option.splits)
        note aux_returnv0[OF this]  
      } note aux_returnv = this

      {
        fix e lv T
        assume "ty_exp \<pi> fd e = return (lv,T)"
        from wf_ty_exp[OF WTM this WFFD] have "wf_ty SM T"
          unfolding wf_rty_def[OF WTM] by simp
      } note [simp] = this

      {
        fix eff c'
        assume "c \<noteq> com.Skip"
        and "cfg_step c = edge.Effect eff c'"
        hence CFG: "cfg c (label.Effect eff) c'"
          by (rule step2cfg1)
        note TYC' = cfg_pres_tycom[OF CFG TYC]  
        note WFC' = cfg_pres_wfcom[OF CFG WFC]  


        from CFG have 
          "nd_spec wt_state (effect \<pi> eff ((fd, c', l, rt) # \<sigma>', \<gamma>, \<mu>))"  
          using WFC TYC WTV
          apply (cases rule: ty_cfg_cases)
          apply (simp_all add: lift_def)

          apply (clarsimp 
            simp: ty_assign_def comp_evs_def
            split: Error_Monad.bind_split_asm)
          apply (e_vcg' simp: ty_assign'_wtD)

          apply (auto simp: wt_val_ty_conv is_Ptr_def) []
          using WFC' TYC' WTG WTL WTFRS FD WTRA
          apply (clarsimp dest!: mem_eqD1 
            simp: wt_state_def wt_valuation_mono wt_stack_frames_mono)

          apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)
            apply (auto simp: wt_stack_frame_def) []
        
          apply (clarsimp 
            simp: ty_assign_def Let_def comp_evs_def
            simp: assert_int_exp_def
            dest: wf_ty_exp
            split: Error_Monad.bind_split_asm)
          apply (rule e_vcg | rule e_cons, rule e_vcg)+
          using WTV WTM WFFD WTFRS WTG WTL WTRA
          apply simp_all
          apply clarsimp
          apply (rule e_vcg | rule e_cons, rule e_vcg)+
          apply simp_all
          apply (rule e_vcg | rule e_cons, rule e_vcg)+
          apply simp_all
          apply (rule e_vcg | rule e_cons, rule e_vcg)+
          apply (simp_all add: nonzero_tyI[OF WF])

          apply clarsimp
          apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)
          apply (rule e_vcg | rule e_cons, rule e_vcg)+
          apply simp
          apply simp
          apply (auto simp add: wt_val_ty_conv ty_assign'_def Let_def) []
          apply simp

          apply (clarsimp dest!: mem_eqD1)
          apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)

          apply (simp add: wt_state_def)
            apply (auto simp: wt_stack_frame_def FD WFC' TYC') []
          apply simp apply simp  
          
          apply (clarsimp 
            simp: ty_assign_def Let_def comp_evs_def is_Ptr_def
            dest: wf_ty_exp
            split: Error_Monad.bind_split_asm)
          apply e_vcg'
          apply (rule WTM)

          using WTG
          apply clarsimp
          apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)
          apply (clarsimp simp: wt_state_def)
            apply (auto simp: wt_stack_frame_def FD WFC' TYC') []

          apply (clarsimp simp: eval_exp'_alt comp_evs_def 
            op_return_def assign_return_value_def)  
          apply (e_vcg')
          apply clarsimp
          apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)
          apply (clarsimp simp: wt_state_def)
          apply (clarsimp simp: wt_raddr_def RT_def split: option.splits)

          using WTG
          apply (clarsimp dest!: mem_eqD1) apply (drule (1) mem_ord_trans)
          apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)
          apply (clarsimp simp: wt_state_def)

          apply (e_vcg' vcg: aux_returnv)

          apply (clarsimp 
            simp: fun_compat_def resolve_fname_def lookup_fun_def eval_exp'_alt comp_evs_def
            simp: Let_def lift'_def args_compat_def ty_assign_def o2e_def
            split: Error_Monad.bind_split_asm option.splits)
          apply (drule return_ty_assignD; assumption?; simp)

          apply (e_vcg' simp del: map_map simp: map_map[symmetric])
          using WFC' TYC' FD
          apply (simp add: wt_state_def wt_stack_frame_def)
          
          apply (clarsimp 
            simp: fun_compatv_def resolve_fname_def lookup_fun_def eval_exp'_alt comp_evs_def
            simp: Let_def lift'_def args_compat_def ty_assign_def o2e_def
            split: Error_Monad.bind_split_asm option.splits)
          apply (e_vcg' simp del: map_map simp: map_map[symmetric])
          using WFC' TYC' FD
          apply (simp add: wt_state_def wt_stack_frame_def)
          
          using WFC' TYC' FD
          apply (simp add: wt_state_def wt_stack_frame_def)
          done
      } note aux_effect = this    
            
      from TYC WTRA have [simp]: "c=com.Skip \<Longrightarrow> rt=None"  
        by (auto simp: ty_com_def wt_raddr_def RT_def split: option.splits)

      {
        fix b c1 c2
        assume NS[simp]: "c\<noteq>com.Skip"
        and STEP: "cfg_step c = edge.Cond b c1 c2"

        from step2cfg2[OF NS STEP] have 
          CFG1: "cfg c (label.Guard (guard.Pos b)) c1"
          and CFG2: "cfg c (label.Guard (guard.Neg b)) c2"
          by auto

        have WTS1: "wt_state (upd_com c1 s)"
          using cfg_pres_tycom[OF CFG1 TYC, simplified] cfg_pres_wfcom[OF CFG1 WFC] 
          WTG FD WTFRS WT_TOP_FR
          by (auto simp: wt_state_def wt_stack_frame_def)

        have WTS2: "wt_state (upd_com c2 s)"
          using cfg_pres_tycom[OF CFG2 TYC, simplified] cfg_pres_wfcom[OF CFG2 WFC] 
          WTG FD WTFRS WT_TOP_FR
          by (auto simp: wt_state_def wt_stack_frame_def)

        from CFG1 WFC TYC have IPE: "assert_int_ptr_exp \<pi> fd b = return ()" 
          by (cases rule: ty_cfg_cases; simp)

        {
          fix ty v
          assume "ty = ty.I \<or> ty = ty.Null \<or> is_Ptr ty"
          and "wt_val SM \<mu> (norm_array_ty ty) v"
          and "v \<noteq> val.Uninit"
          hence "nd_spec (\<lambda>_. True) (to_bool_aux \<mu> v)"
            apply (auto simp: wt_val_ty_conv is_Ptr_def)
            apply e_vcg'
            done
        } note [e_vcg] = this 


        have "nd_spec
          (\<lambda>bv. nd_spec wt_state
                (do {
                   x \<leftarrow> to_rval' s bv;
                   bv \<leftarrow> to_bool_aux' s x;
                   if bv
                   then return (upd_com c1 s)
                   else return (upd_com c2 s)
                 }))
          (eval_exp (\<gamma> ++ l) \<mu> b)"
          using IPE WTV 
          apply (clarsimp 
            simp: assert_int_ptr_exp_def 
            simp: to_rval'_def to_bool_aux'_def
            split: Error_Monad.bind_split_asm)
          using WTS1 WTS2
          apply e_vcg'
          done        
      } note aux_guard = this    

      show ?thesis
        apply (e_vcg' simp: ss_step_def eval_exp'_def Let_def)
        apply (clarsimp_all simp: Let_def)

        using aux_return_skip apply simp

        using aux_effect apply simp

        using aux_guard apply (simp add: lift'_def comp_evs_def cong: if_cong) 
        done
    qed    

    theorem initial_state_spec[e_vcg]: 
      -- \<open>Main theorem: Initial state is well-typed\<close>
      "nd_spec wt_state (initial_state \<pi>)"
    proof -
      have [simp]: 
        "lookup_fun \<pi> main_fname = return main_fd"
        using main_exists
        by (auto simp: lookup_fun_def)

      from wf_fdeclI[OF main_exists] have 
        [simp]: 
          "wf_vdecls SM (fun_decl.locals main_fd)" 
        by (auto simp: wf_fun_decl_def)

      show ?thesis
        unfolding initial_state_def create_frame_def
        apply (e_vcg' simp: wf_vdecls)
        apply clarsimp
        apply ((drule (1) tagged_monos)+; unfold ID_TAG_def)+
        (* TODO/FIXME: Two notions for fun exists: Via FM, and via set functs!*)
        using wf_fdeclI[OF main_exists] ty_fdeclI[OF main_exists]
        apply (clarsimp 
          simp: wt_state_def wt_stack_frame_def 
          simp: wf_fun_decl_def ty_fdecl_def
          split: Error_Monad.bind_split_asm)
        using main_exists
        apply (auto simp: mk_fun_map_def dest: map_of_SomeD)
        done
    qed    

    lemma small_steps_pres_wt_state:
      assumes "nd_spec wt_state s"
      assumes "small_steps \<pi> s s'"
      shows "nd_spec wt_state s'"
      using assms(2,1) 
      apply (induction rule: star.induct)
      apply simp
      apply (clarsimp elim!: small_step'.cases)
      apply (frule ss_imp_no_empty)
      apply (clarsimp simp: small_step_iff_ss_step)
      apply rprems
      apply e_vcg'
      done
      
    theorem interp_spec:
      -- \<open>Main theorem: Interpretation yields no static errors 
          and preserves typing\<close>
      assumes "wt_state s"
      shows "e_spec wt_state is_EDynamic (\<not>terminates \<pi> s) (interp \<pi> s)"  
    proof (cases "interp \<pi> s = ENonterm")
      case True with interp_correct have "\<not>terminates \<pi> s"
        by simp
      with True show ?thesis by simp  
    next
      case False with interp_correct have "yields \<pi> s (interp \<pi> s)" by simp
      hence "small_steps \<pi> (return s) (interp \<pi> s)" by (auto simp: yields_def)
      from small_steps_pres_wt_state[OF _ this] assms False
      show ?thesis by (auto simp: pw_espec_iff)
    qed  
  end

  (* TODO/FIXME: Consider monad that always terminates, or
    automatic syntactic termination check with def-unfolding! *)  

  lemma [simp]: "norm_struct_ptr \<pi> rty \<noteq> ENonterm"  
    by (case_tac "rty" rule: norm_struct_ptr.cases;
      auto split: Error_Monad.bind_splits)

  lemma [simp]: "ty_exp_aux \<pi> fd e \<noteq> ENonterm"
    apply (induction e)
    apply (simp_all split: Error_Monad.bind_split, safe, simp_all)

    apply (rename_tac f; case_tac f; 
      auto split: Error_Monad.bind_splits simp: varty_def)

    apply (rename_tac f e lv v; case_tac "(f,(lv,v))" rule: ty_op1.cases; 
      auto split: Error_Monad.bind_splits simp: resolve_mname_def)

    apply (rename_tac f e lv1 v1 lv2 v2; 
      case_tac f; 
      auto 
        split: Error_Monad.bind_splits option.splits
        simp: resolve_mname_def ty_op2_def)
    done  

  lemma [simp]: "ty_exp \<pi> fd e \<noteq> ENonterm"
    by (auto simp: ty_exp_def split: error.splits pre_error.splits ck_error.splits option.splits)  


  lemma [simp]: "ty_com1 \<pi> fd c \<noteq> ENonterm"
    apply (induction c rule: ty_com1.induct)
    by (auto 
      simp: ty_assign_def ty_assign'_def Let_def
      simp: assert_int_ptr_exp_def assert_int_exp_def
      simp: fun_compat_def fun_compatv_def resolve_fname_def args_compat_def
      dest!: emap_nontermD'
      split: Error_Monad.bind_split
      )

  lemma [simp]: "ty_com \<pi> fd c \<noteq> ENonterm"
    by (auto 
      simp: ty_com_def assert_def
      split: Error_Monad.bind_split)
    

  lemma [simp]: "ty_fdecl \<pi> fd \<noteq> ENonterm"
    by (auto 
      simp: ty_fdecl_def 
      dest!: efold_nontermD'
      split: Error_Monad.bind_split option.split)  

  lemma [simp]: "wt_program \<pi> \<noteq> ENonterm"
    by (auto 
      simp: wt_program_def ty_program_def
      dest!: efold_nontermD'
      split: Error_Monad.bind_split option.splits
      split: error.splits pre_error.splits ck_error.splits
      )  

  theorem check_execute_spec:
    -- \<open>Main theorem: Check-Execute yields no static errors\<close>  
    shows "e_spec 
      (\<lambda>_. True) 
      (\<lambda>Inl _ \<Rightarrow> True | Inr e \<Rightarrow> is_EDynamic e) 
      (\<exists>s. initial_state \<pi> = return s \<and> \<not>terminates \<pi> s) 
      (check_execute \<pi>)"
    unfolding check_execute_def
    apply (cases "wt_program \<pi>")
    defer
    apply e_vcg'
    apply e_vcg'
    apply simp
    apply (e_vcg' 
      vcg: wt_program_loc.initial_state_spec[THEN espec_add_ret] wt_program_loc.interp_spec)
    apply (unfold_locales; auto simp: wt_program_def split: Error_Monad.bind_splits)
    apply (unfold_locales; auto simp: wt_program_def split: Error_Monad.bind_splits)
    done

end

