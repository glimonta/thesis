theory SmallStep
imports
  "~~/src/HOL/IMP/Star"
  "~~/src/HOL/Library/While_Combinator"
  Stack CFG
begin
  
  definition lift :: "(valuation \<Rightarrow> memory \<hookrightarrow> memory) \<Rightarrow> state \<hookrightarrow> state"
    where "lift f \<equiv> \<lambda>(stk,\<gamma>,\<mu>). do {
      let ev = comp_evs stk \<gamma>;
      \<mu> \<leftarrow> f ev \<mu>;
      return (stk,\<gamma>,\<mu>)
    }"

  definition lift' :: "(valuation \<Rightarrow> memory \<hookrightarrow> 'a) \<Rightarrow> state \<hookrightarrow> 'a"  
    where "lift' f \<equiv> \<lambda>(stk,\<gamma>,\<mu>). f (comp_evs stk \<gamma>) \<mu>"

  definition to_rval' :: "state \<Rightarrow> res \<hookrightarrow> val" where
    "to_rval' \<equiv> \<lambda>(stk,\<gamma>,\<mu>) r. to_rval \<mu> r"

  definition to_bool_aux' :: "state \<Rightarrow> val \<hookrightarrow> bool" where
    "to_bool_aux' \<equiv> \<lambda>(stk,\<gamma>,\<mu>) r. to_bool_aux \<mu> r"
 

  definition eval_exp' :: "state \<Rightarrow> exp \<hookrightarrow> res" where
    "eval_exp' \<equiv> \<lambda>s e. lift' (\<lambda>ev \<mu>. eval_exp ev \<mu> e) s"

  lemma eval_exp'_alt: "eval_exp' = (\<lambda>(stk,\<gamma>,\<mu>) e. eval_exp (comp_evs stk \<gamma>) \<mu> e)"
    by (auto simp: eval_exp'_def lift'_def)

  primrec basic_effect :: "bcom \<Rightarrow> valuation \<Rightarrow> memory \<hookrightarrow> memory" where
    "basic_effect (bcom.Assign l r) ev \<mu> = do {
      l \<leftarrow> eval_exp ev \<mu> l;
      l \<leftarrow> to_lval l;
      r \<leftarrow> eval_exp ev \<mu> r;
      r \<leftarrow> to_rval \<mu> r;
      \<mu> \<leftarrow> eset (l_addr l) r \<mu>;
      return \<mu>
    }"
  | "basic_effect (bcom.Malloc e1 T e2) ev \<mu> = do {
      e1 \<leftarrow> eval_exp ev \<mu> e1;
      e1 \<leftarrow> to_lval e1;
      e2 \<leftarrow> eval_exp ev \<mu> e2;
      e2 \<leftarrow> to_int \<mu> e2;
      let e2 = sint e2;
      assert (e2\<ge>0) overflow_error;  (* Note: calloc asserts positive size *)
      (addr,\<mu>) \<leftarrow> calloc T False (nat e2) \<mu>;
      \<mu> \<leftarrow> eset (l_addr e1) (val.Addr addr) \<mu>;
      return \<mu>
    }"  
  | "basic_effect (bcom.Free e) ev \<mu> = do {
      e \<leftarrow> eval_exp ev \<mu> e;
      e \<leftarrow> to_ptr \<mu> e;
      \<mu> \<leftarrow> free False e \<mu>;
      return \<mu>
    }"  

  term eval_exp  

  definition lookup_fun :: "program \<Rightarrow> fname \<hookrightarrow> fun_decl" where
    "lookup_fun p f \<equiv> elookup (\<lambda>_. type_error) (mk_fun_map p) f"

  definition eval_args :: "exp list \<Rightarrow> valuation \<Rightarrow> memory \<hookrightarrow> val list" where
    "eval_args args ev \<mu> \<equiv> emap (eval_exp ev \<mu> #> to_rval \<mu>) args"

  abbreviation "eval_args' args \<equiv> lift' (eval_args args)"


  primrec func_effect :: "program \<Rightarrow> fcom \<Rightarrow> state \<hookrightarrow> state" where
    "func_effect p (fcom.Return e) s = do {
      e \<leftarrow> eval_exp' s e;
      op_return (Some e) s
    }"
  | "func_effect p (fcom.Returnv) s = do {
      op_return None s
    }"
  | "func_effect p (fcom.Callfun e f args) s = do {
      fd \<leftarrow> lookup_fun p f;
      e \<leftarrow> eval_exp' s e;
      e \<leftarrow> to_lval e;
      args \<leftarrow> eval_args' args s;
      op_call (Some e) fd args s
    }"  
  | "func_effect p (fcom.Callfunv f args) s = do {
      fd \<leftarrow> lookup_fun p f;
      args \<leftarrow> eval_args' args s;
      op_call None fd args s
    }"  
  
  primrec effect :: "program \<Rightarrow> effect \<Rightarrow> state \<hookrightarrow> state" where
    "effect p (effect.Basic c) s = lift (basic_effect c) s" 
  | "effect p (effect.Func c) s = func_effect p c s"  
  | "effect p (effect.Skip) s = return s"

  primrec eval_guard :: "guard \<Rightarrow> state \<hookrightarrow> bool" where
    "eval_guard (guard.Pos e) s = do {
      b \<leftarrow> eval_exp' s e;
      b \<leftarrow> (to_rval' s #> to_bool_aux' s) b;
      return b
    }" 
  | "eval_guard (guard.Neg e) s = do {
      b \<leftarrow> eval_exp' s e;
      b \<leftarrow> (to_rval' s #> to_bool_aux' s) b;
      return (\<not>b)
    }"
 
  fun com_of :: "state \<Rightarrow> com option" where
    "com_of ((_,c,_,_)#_,_,_) = Some c"
  | "com_of _ = None"  

  fun upd_com :: "com \<Rightarrow> state \<Rightarrow> state" where
    "upd_com c ((fd,_,l,r)#stk,\<gamma>,\<mu>) = ((fd,c,l,r)#stk,\<gamma>,\<mu>)"
  | "upd_com c ([],_,_) = undefined"  

  inductive small_step :: "program \<Rightarrow> state \<Rightarrow> state ce \<Rightarrow> bool" for p where
    ss_effect: "\<lbrakk> com_of s = Some c; cfg c (label.Effect e) c'; s' = effect p e (upd_com c' s) \<rbrakk> \<Longrightarrow> small_step p s s'"
  | ss_guard: "\<lbrakk> com_of s = Some c; cfg c (label.Guard g) c'; eval_guard g s = return True \<rbrakk> \<Longrightarrow> small_step p s (return ((upd_com c' s)))"
  | ss_failed_guard: "\<lbrakk> com_of s = Some c; cfg c (label.Guard g) c'; eval_guard g s = EAssert e \<rbrakk> \<Longrightarrow> small_step p s (EAssert e)"
  | ss_return_void: "\<lbrakk> com_of s = Some com.Skip; s' = op_return None s \<rbrakk> \<Longrightarrow> small_step p s s'"


  lemma [simp]: "\<not>is_nonterm (mk_repr x)"
    unfolding mk_repr_def by auto
  
  lemma [simp]: "\<not>is_nonterm (eval0 ev op0)"
    by (induction op0) (auto split: option.splits)
    
  lemma [simp]: "is_nonterm (eget (l1 o\<^sub>l l2) v) \<longleftrightarrow> (is_nonterm (eget l1 v) \<or> 
    (\<exists>y. is_res (eget l1 v) y \<and> is_nonterm (eget l2 y)))"  
    unfolding ecompose_def
    by auto

  lemma [simp]: "is_nonterm (eset (l1 o\<^sub>l l2) b a) \<longleftrightarrow> is_nonterm (eget l1 a) \<or> 
    (\<exists>y. is_res (eget l1 a) y \<and> (is_nonterm (eset l2 b y) \<or> (\<exists>ya. is_res (eset l2 b y) ya \<and>
        is_nonterm (eset l1 ya a))))"  
    unfolding ecompose_def
    by auto

    
  lemma no_nonterm_espec_conv: "\<not>is_nonterm m \<longleftrightarrow> e_spec (\<lambda>_. True) (\<lambda>_. True) False m"  
    by (simp add: pw_espec_iff)

  lemma [simp]: "\<not>is_nonterm (eget (l_C1_lens isC theC C e) v)"
    unfolding l_C1_lens_def by auto

  lemma [simp]: "\<not>is_nonterm (eset (l_C1_lens isC theC C e) b a)"
    unfolding l_C1_lens_def by auto

  lemma [simp]: "\<not>is_nonterm (cnv_array_to_eptr \<mu> addr)"  
    by (auto simp: cnv_array_to_eptr_def split: prod.splits)

  lemma [simp]: "\<not>is_nonterm (to_rval \<mu> v)" by (cases v) (auto)

  lemma [simp]: "\<not>is_nonterm (to_int_aux x)"
    by (cases x) auto

  lemma [simp]: "\<not>is_nonterm (to_bool_aux \<mu> x)"
    by (cases x) auto

  lemma [simp]: "\<not>is_nonterm (to_int \<mu> x)"  
    by (auto simp: to_int_def)

  lemma [simp]: "\<not>is_nonterm (ref_op x)"  
    by (cases x) auto

  lemma [simp]: "\<not>is_nonterm (elookup E m x)"
    by (auto simp: elookup_def split: option.split)  

  lemma [simp]: "\<not>is_nonterm (memb_op \<mu> name r)"  
    by (cases "(name,r)" rule: memb_op.cases) 
    (auto simp: memb_addr_def l_raw_mem_def l_nth_def 
      memb_subpath_def Let_def)

  lemma [simp]: "\<not>is_nonterm (to_ptr \<mu> v)"  
    by (auto simp: to_ptr_def split: val.splits)

  lemma [simp]: "\<not>is_nonterm (deref_op ev y)"  
    by (auto simp: deref_op_def split: val.splits)

  lemma [simp]: "\<not>is_nonterm (membp_op \<mu> name r)"  
    by (auto simp: memb_addr_def l_raw_mem_def l_nth_def 
      memb_subpath_def Let_def membp_op_def)

  lemma [simp]: "\<not>is_nonterm (eval1 ev op1 x1)"
    apply (induction op1) 
    apply (auto split: option.splits
      simp: un_arith_op_def iop_uminus_def iop_Not_def iop_BNot_def)
    done

  lemma [simp]: "\<not>is_nonterm (index_addr \<mu> i addr)"  
    by (auto simp: index_addr_def l_raw_mem_def l_nth_def 
      index_subpath_def resolve_subpath_array_def l_last_def l_butlast_def Let_def
        split: split_if_asm prod.splits)

  lemma [simp]: "\<not>is_nonterm (plus_op \<mu> x1 x2)"  
    apply (cases "(x1,x2)" rule: plus_op.cases)
    apply (auto simp: iop_plus_def)
    done

  lemma [simp]: "\<not>is_nonterm (minus_op \<mu> x1 x2)"  
    apply (cases "(x1,x2)" rule: minus_op.cases)
    apply (auto simp: l_raw_mem_def l_nth_def 
      index_subpath_def resolve_subpath_array_def l_last_def l_butlast_def Let_def
        iop_minus_def diff_addr_def diff_subpath_def
        split: split_if_asm)
    done

  lemma [simp]: "\<not>is_nonterm (index_op ev x1 x2)"  
    by (auto simp: index_op_def split: res.splits val.splits)

  lemma [simp]: "\<not>is_nonterm (compare_addr \<mu> x1 x2)" 
    by (auto simp: compare_addr_def split: prod.splits list.splits subscript.splits)

  lemma [simp]: "\<not>is_nonterm (less_op \<mu> x1 x2)"  
    apply (induction x1 x2 rule: less_op.induct)
    apply (auto simp: addr_less_def iop_less_def split: ptr_comp_res.splits)
    done

  lemma [simp]: "\<not>is_nonterm (le_op \<mu> x1 x2)"  
    apply (induction x1 x2 rule: le_op.induct)
    apply (auto simp: addr_leq_def iop_le_def split: ptr_comp_res.splits)
    done

  lemma [simp]: "\<not>is_nonterm (eq_op \<mu> x1 x2)"  
    apply (induction x1 x2 rule: eq_op.induct)
    apply (auto simp: iop_eq_def addr_eq_def split: split_if_asm ptr_comp_res.splits)
    done

  lemma [simp]: "\<not>is_nonterm (eval2 ev op2 x1 x2)"
    apply (induction op2) 
    apply (auto split: option.splits 
      simp: rvop2_def bin_arith_op_def
      simp: iop_mult_def iop_div_def iop_mod_def iop_less_def iop_le_def iop_eq_def
      iop_And_def iop_Or_def iop_BAnd_def iop_BOr_def iop_BXor_def)
    done


  lemma [simp]: "\<not>is_nonterm (eval_exp ev \<mu> e)"
    apply (induction e)
    apply auto
    done

  lemma [simp]: "\<not>is_nonterm (to_lval x)"  
    by (cases x) (auto)

  lemma [simp]: "\<not>is_nonterm (free allow_static addr \<mu>)" 
    by (auto simp: Let_def free_def raw_free_def split: prod.splits)

  lemma [simp]: "\<not>is_nonterm (alloc T static \<mu>)"  
    by (auto simp: alloc_def raw_alloc_def)

  lemma [simp]: "\<not>is_nonterm (calloc T static n \<mu>)"  
    by (auto simp: calloc_def raw_alloc_def)

  lemma effect_term[simp]: "\<not>is_nonterm (effect p e s)"
    apply (cases e; simp)
    apply (rename_tac be; case_tac be; auto simp add: lift_def Let_def split: prod.splits)
    apply (rename_tac fe; case_tac fe; auto simp: eval_exp'_def 
      simp: op_return_def lookup_fun_def Let_def assign_return_value_def
      simp: destroy_frame_def to_rval'_def op_call_def create_frame_def
        alloc_params_def cp_alloc_def raw_alloc_def alloc_vdecls_def lift'_def eval_args_def
      dest!: efold_nontermD emap_nontermD
      split: prod.splits option.splits)
    done 
    
  fun is_empty_stack :: "state \<Rightarrow> bool" where
    "is_empty_stack (stk,_) \<longleftrightarrow> stk=[]"

  lemma eval_guard_conv: "eval_guard (guard.Pos b) s = return bv 
      \<longleftrightarrow> eval_guard (guard.Neg b) s = return (\<not>bv)"  
    apply (simp add: eval_guard_def)
    apply (simp split: Error_Monad.bind_split)
    done

  lemma small_step_stuck_empty_aux: 
    "\<exists>s'. small_step p ((fd,c,l,r)#stk,\<gamma>,\<mu>) s'" (is "\<exists>_. small_step p ?s _")
  proof (cases c rule: cfg_outgoing_cases[case_names Skip Effect Guard])
    case Skip thus ?thesis by (auto intro!: ss_return_void)
  next  
    case (Effect e c')
    hence C: "cfg c (label.Effect e) c'"
      by (auto simp: cfg_outgoing_def)
    from ss_effect[OF _ C refl] show ?thesis by force
  next  
    case (Guard b c1 c2)
    hence CP: "cfg c (label.Guard (guard.Pos b)) c1" and
      CN: "cfg c (label.Guard (guard.Neg b)) c2"
      by (auto simp: cfg_outgoing_def)
      
    show ?thesis proof (cases "eval_guard (guard.Pos b) ?s")
      case (return bv)
      show ?thesis proof (cases bv)  
        case True 
        from ss_guard[OF _ CP return[simplified True]]
        show ?thesis by auto
      next
        case False
        with return have "eval_guard (guard.Neg b) ?s = return True"
          by (simp add: eval_guard_conv del: eval_guard.simps)
        from ss_guard[OF _ CN this]
        show ?thesis by auto
      qed
    next  
      case (EAssert e) 
      from ss_failed_guard[OF _ CP this]
      show ?thesis by auto
    next  
      case ENonterm hence "is_nonterm (eval_guard (guard.Pos b) ?s)" by simp
      hence False by (auto simp: eval_guard_def eval_exp'_alt to_rval'_def to_bool_aux'_def)
      thus ?thesis ..
    qed  
  qed  

  
  theorem ss_stuck_empty: "\<not>(\<exists>s'. small_step p s s') \<longleftrightarrow> is_empty_stack s"
    -- \<open>Execution only gets stuck at empty stack\<close>
    apply (cases s rule: com_of.cases)
    apply (auto elim: small_step.cases simp: small_step_stuck_empty_aux)
    done

  corollary ss_imp_no_empty: "small_step \<pi> s s' \<Longrightarrow> \<not>is_empty_stack s"
    using ss_stuck_empty[of \<pi> s] by auto


  definition ss_step :: "program \<Rightarrow> state \<hookrightarrow> state" where
    "ss_step p s \<equiv> do {
      let c = the (com_of s);
      if c=com.Skip then
        op_return None s
      else
        case cfg_step c of 
          edge.Effect e c' \<Rightarrow> do {
            let s = upd_com c' s;
            s \<leftarrow> effect p e s;
            return s
          }
        | (edge.Cond b c1 c2) \<Rightarrow> do {
            b \<leftarrow> eval_exp' s b;
            b \<leftarrow> (to_rval' s #> to_bool_aux' s) b;
            if b then return (upd_com c1 s) else return (upd_com c2 s)
          }
    }"

  lemma [simp]: "eval_exp' s e \<noteq> ENonterm"  
    by (simp add: pw_nt_iff eval_exp'_alt split: prod.splits)

  lemma [simp]: "to_rval' s v \<noteq> ENonterm"  
    by (simp add: pw_nt_iff to_rval'_def split: prod.splits)
    
  lemma [simp]: "to_int_aux v \<noteq> ENonterm"  
    by (simp add: pw_nt_iff split: prod.splits)

  lemma [simp]: "to_bool_aux \<mu> v \<noteq> ENonterm"  
    by (simp add: pw_nt_iff split: prod.splits)


  lemma small_step_iff_ss_step: "\<not>is_empty_stack s \<Longrightarrow> small_step p s s' \<longleftrightarrow> ss_step p s = s'"  
    apply (rule iffI)
    apply (auto elim!: cfg2step small_step.cases) []
    apply (auto simp: ss_step_def) []
    apply (simp add: ss_step_def pw_eq_iff; metis) []
    apply (simp add: ss_step_def pw_eq_iff; metis) []
    apply (simp add: ss_step_def pw_eq_iff; metis) []
    apply (simp add: ss_step_def pw_eq_iff; metis) []
    apply (auto simp: ss_step_def) []

    apply hypsubst
    apply (thin_tac "s'=_")
    apply (cases s rule: com_of.cases; simp)
    apply (clarsimp simp: ss_step_def
      simp del: cfg_step.simps
      split: edge.splits; safe)
    apply (auto simp del: cfg_step.simps intro: ss_return_void) []
    apply (auto simp del: cfg_step.simps intro: ss_effect step2cfg1) []
    apply (auto simp del: cfg_step.simps intro: ss_return_void) []

    apply (drule (1) step2cfg2; clarsimp) 
    apply (auto simp: small_step.simps to_bool_aux'_def split: Error_Monad.bind_splits)
    done


  export_code ss_step checking SML


  subsection \<open>Executions\<close>
  context fixes p :: program begin

  text \<open>We lift our definition of small step to state option in order to be able to take
    more than one step in the semantics.\<close>
  inductive
    small_step' :: "(state) ce \<Rightarrow> (state) ce \<Rightarrow> bool"
  where
    "small_step p s s' \<Longrightarrow> small_step' (return s) s'"
  
  abbreviation
    small_steps :: "(state) ce \<Rightarrow> (state) ce \<Rightarrow> bool"
      where "small_steps x y == star small_step' x y"


  text \<open>A state is considered final if the stack in that state is empty or if it's an error state.\<close>
  fun is_term :: "state ce \<Rightarrow> bool" where
    "is_term (return s) = is_empty_stack s"
  | "is_term _ = True"

  text \<open>Final states are exactly the states where the semantics is stuck\<close>
  lemma is_term_no_step: "is_term s \<longleftrightarrow> \<not>(\<exists>s'. small_step' s s')"
    apply (cases s)
    using ss_stuck_empty[symmetric]
    apply (auto simp: small_step'.simps)
    done
  
  lemma not_is_term_conv: "\<not>is_term ss \<longleftrightarrow> (\<exists>s. ss=return s \<and> \<not>is_empty_stack s)"
    apply (cases ss) by auto  

  definition yields :: "state \<Rightarrow> state ce \<Rightarrow> bool" 
    -- \<open>Final state of execution from start state\<close>
  where
    "yields s s' \<equiv> small_steps (return s) s' \<and> is_term s'"

  definition terminates :: "state \<Rightarrow> bool" where
    "terminates s \<equiv> \<exists>s'. yields s s'"


  partial_function (error) interp where "
    interp s = (
      if is_term (return s) then
        return s
      else do {
        s \<leftarrow> ss_step p s;
        interp s
      }
    )"

  lemmas [code] = interp.simps  

  lemma [simp]: "small_steps (EAssert e) s' \<longleftrightarrow> s'=EAssert e"
    by (auto elim: star.cases simp: small_step'.simps)

  lemma [simp]: "\<not>is_nonterm (op_return v s)"
    by (auto simp: 
      simp: op_return_def Let_def assign_return_value_def
      simp: destroy_frame_def to_rval'_def 
      dest!: efold_nontermD 
      split: prod.splits option.splits edge.splits)

  lemma [simp]: "\<not>is_nonterm (ss_step p s)"
    by (auto simp: ss_step_def eval_exp'_alt
      simp: lookup_fun_def Let_def 
      simp:  to_rval'_def op_call_def create_frame_def
        alloc_params_def cp_alloc_def raw_alloc_def alloc_vdecls_def
        to_bool_aux'_def
      split: prod.splits option.splits edge.splits)

  lemma [simp]: "ss_step p s \<noteq> ENonterm"
    by (simp add: pw_nt_iff)  

  lemma yields_interp_aux: "yields s s' \<Longrightarrow> interp s = s'"
  proof -  
    assume "yields s s'"
    hence "small_steps (return s) s'" "is_term s'" unfolding yields_def by auto
    thus "interp s = s'"
      apply (induction "(return s)::_ ce" s' arbitrary: s rule: star.induct)
      apply (subst interp.simps; simp)
      apply (subst interp.simps; auto simp: small_step'.simps)
      apply (meson is_empty_stack.simps is_term.simps(1) is_term_no_step small_step'.intros)
      apply (subst (asm) small_step_iff_ss_step; simp)
      apply (auto split: Error_Monad.bind_splits)
      done
  qed    

  lemma yields_interp: "terminates s \<Longrightarrow> yields s s' \<longleftrightarrow> s' = interp s"
    unfolding terminates_def
    by (auto dest: yields_interp_aux)
    

  lemma terminates_empty: "is_empty_stack s \<Longrightarrow> terminates s"  
    unfolding terminates_def yields_def
    by auto

  lemma terminates_step_err: 
    "\<lbrakk>\<not> is_empty_stack s; ss_step p s = EAssert e\<rbrakk> 
    \<Longrightarrow> terminates s"
    unfolding terminates_def yields_def
    apply (auto simp: small_step_iff_ss_step[symmetric])
    using SmallStep.small_step'.intros is_term.simps(2) by blast
    
  lemma terminates_step_ret: 
    "\<lbrakk>\<not> is_empty_stack s; ss_step p s = return s'; terminates s'\<rbrakk> 
    \<Longrightarrow> terminates s"
    unfolding terminates_def yields_def
    apply (auto simp: small_step_iff_ss_step[symmetric])
    by (meson small_step'.intros star.step)


  lemma nonterm_interp: "\<not>terminates s \<Longrightarrow> interp s = ENonterm"    
  proof (rule ccontr)
    {
      fix t
      assume "interp s = ETerm t"
      hence "local.terminates s"
        apply (rule interp.raw_induct[rotated])
        apply (auto 
          split: split_if_asm Error_Monad.bind_splits
          simp: terminates_empty terminates_step_err terminates_step_ret)
        done
    } moreover assume "\<not> local.terminates s" "local.interp s \<noteq> ENonterm"
    ultimately show False by (cases "local.interp s") auto
  qed  

  lemma small_steps_preserve_nonterm:
    assumes "\<not>is_nonterm s" 
    assumes "small_steps s s'"
    shows "\<not>is_nonterm s'"
    using assms(2,1)
    apply (induction rule: star.induct)
    by (auto simp: small_step'.simps small_step.simps)

  lemma yields_no_nonterm: "yields s s' \<Longrightarrow> \<not>is_nonterm s'" 
    unfolding yields_def using small_steps_preserve_nonterm[of "return s" s']
    by auto 

  lemma interp_nonterm: "interp s = ENonterm \<Longrightarrow> \<not>terminates s"
    using yields_no_nonterm[of s]
    by (auto simp: terminates_def pw_nt_iff dest: yields_interp_aux)
    
  theorem interp_correct: 
    "interp s = ENonterm \<longleftrightarrow> \<not>terminates s"  
    "interp s \<noteq> ENonterm \<longleftrightarrow> yields s (interp s)"
    using nonterm_interp[of s] interp_nonterm[of s] 
    apply blast
    by (metis nonterm_interp yields_interp_aux yields_no_nonterm 
      is_nonterm.simps(1) terminates_def)

end

export_code interp checking SML


end

