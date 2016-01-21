section \<open>Error Monad\<close>
theory Error_Monad
imports  
  "~~/src/HOL/Library/Monad_Syntax"
  "$AFP/Automatic_Refinement/Lib/Refine_Lib"
begin

(*
  notation (input)
    bind_do (infixr "\<bind>" 54) (* TODO: Replace by new \<bind> symbol *)
*)

  text \<open>We define an error monad, with a special case for nontermination,
    and set up the monad syntax and partial function package\<close>

  subsection \<open>Basic type definition\<close>
  datatype ('a,'b) pre_error = pre_return 'a | pre_EAssert 'b

  datatype ('a,'b) error = ETerm "('a,'b) pre_error" | ENonterm

  abbreviation "return x \<equiv> ETerm (pre_return x)"
  abbreviation "EAssert x \<equiv> ETerm (pre_EAssert x)"

  lemma error_cases: obtains 
    x where "v=return x" | e where "v=EAssert e" | "v=ENonterm"
    apply (cases v; simp) apply (rename_tac x; case_tac x; simp)
    done

  lemmas [cases type] = error_cases[case_names return EAssert ENonterm] 


  context begin
    qualified fun bind where
      "bind (return x) f = f x"
    | "bind (EAssert e) _ = EAssert e"
    | "bind (ENonterm) _ = ENonterm"

  end  

  adhoc_overloading bind Error_Monad.bind

  subsection \<open>Monad Laws and Basic Lemmas\<close>

  lemma monad_laws[simp]: 
    "return x \<bind> f = f x"
    "m \<bind> return = m"
    "(m \<bind> f) \<bind> g = m \<bind> (\<lambda>x. f x \<bind> g)"
    apply simp
    apply (cases m; simp)+
    done


  context begin  
    qualified lemma bind_split: 
      "P (m \<bind> f) = ((\<forall>e. m = EAssert e \<longrightarrow> P (EAssert e)) \<and> (m=ENonterm \<longrightarrow> P (ENonterm)) \<and> (\<forall>v. m = return v \<longrightarrow> P (f v)))"  
      apply (cases m) by auto
  
    qualified lemma bind_split_asm: "P (m \<bind> f) 
      = (\<not> ((\<exists>e. m = (EAssert e) \<and> \<not> P (EAssert e)) \<or> (m=ENonterm \<and> \<not>P ENonterm) \<or> (\<exists>x. m = return x \<and> \<not> P (f x))))"  
      apply (cases m) by auto
  
    qualified lemmas bind_splits = bind_split bind_split_asm  
  end

  subsection \<open>Partial Function Setup\<close>  
  abbreviation "error_ord \<equiv> flat_ord ENonterm"
  abbreviation "mono_error \<equiv> monotone (fun_ord error_ord) error_ord"

  interpretation error:
    partial_function_definitions "flat_ord ENonterm" "flat_lub ENonterm"
    rewrites "flat_lub ENonterm {} \<equiv> ENonterm"
  by (rule flat_interpretation)(simp add: flat_lub_def)


  thm option.leq_trans

  lemma bind_mono[partial_function_mono]:
  fixes B :: "('a \<Rightarrow> ('b, 'err) error) \<Rightarrow> ('d, 'err) error"
  assumes mf: "mono_error B" and mg: "\<And>y. mono_error (\<lambda>f. C y f)"
  shows "mono_error (\<lambda>f. Error_Monad.bind (B f) (\<lambda>y. C y f))"
  proof (rule monotoneI)
    fix f g :: "'a \<Rightarrow> ('b,'err) error" assume fg: "fun_ord error_ord f g"
    with mf
    have "error_ord (B f) (B g)" by (rule monotoneD[of _ _ _ f g])
    then have "error_ord (Error_Monad.bind (B f) (\<lambda>y. C y f)) (Error_Monad.bind (B g) (\<lambda>y. C y f))"
      unfolding flat_ord_def by auto    
    also from mg
    have "\<And>y'. error_ord (C y' f) (C y' g)"
      by (rule monotoneD) (rule fg)
    then have "error_ord (Error_Monad.bind (B g) (\<lambda>y'. C y' f)) (Error_Monad.bind (B g) (\<lambda>y'. C y' g))"
      unfolding flat_ord_def by (cases "B g") auto
    finally (error.leq_trans)
    show "error_ord (Error_Monad.bind (B f) (\<lambda>y. C y f)) (Error_Monad.bind (B g) (\<lambda>y'. C y' g))" .
  qed

  
  lemma error_admissible: "error.admissible (%(f::'a \<Rightarrow> ('b,'err) error).
    (\<forall>x y. f x = ETerm y \<longrightarrow> P x y))"
  proof (rule ccpo.admissibleI)
    fix A :: "('a \<Rightarrow> ('b,'err) error) set"
    assume ch: "Complete_Partial_Order.chain error.le_fun A"
      and IH: "\<forall>f\<in>A. \<forall>x y. f x = ETerm y \<longrightarrow> P x y"
    from ch have ch': "\<And>x. Complete_Partial_Order.chain error_ord {y. \<exists>f\<in>A. y = f x}" by (rule chain_fun)
    show "\<forall>x y. error.lub_fun A x = ETerm y \<longrightarrow> P x y"
    proof (intro allI impI)
      fix x y assume "error.lub_fun A x = ETerm y"
      from flat_lub_in_chain[OF ch' this[unfolded fun_lub_def]]
      have "ETerm y \<in> {y. \<exists>f\<in>A. y = f x}" by simp
      then have "\<exists>f\<in>A. f x = ETerm y" by auto
      with IH show "P x y" by auto
    qed
  qed
  
  lemma fixp_induct_error:
    fixes F :: "'c \<Rightarrow> 'c" and
      U :: "'c \<Rightarrow> 'b \<Rightarrow> ('a,'err) error" and
      C :: "('b \<Rightarrow> ('a,'err) error) \<Rightarrow> 'c" and
      P :: "'b \<Rightarrow> ('a,'err) pre_error \<Rightarrow> bool"
    assumes mono: "\<And>x. mono_error (\<lambda>f. U (F (C f)) x)"
    assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub (flat_lub ENonterm)) (fun_ord error_ord) (\<lambda>f. U (F (C f))))"
    assumes inverse2: "\<And>f. U (C f) = f"
    assumes step: "\<And>f x y. (\<And>x y. U f x = ETerm y \<Longrightarrow> P x y) \<Longrightarrow> U (F f) x = ETerm y \<Longrightarrow> P x y"
    assumes defined: "U f x = ETerm y"
    shows "P x y"
    using step defined error.fixp_induct_uc[of U F C, OF mono eq inverse2 error_admissible]
    unfolding fun_lub_def flat_lub_def by(auto 9 2)
  
  declaration {* Partial_Function.init "error" @{term error.fixp_fun}
    @{term error.mono_body} @{thm error.fixp_rule_uc} @{thm error.fixp_induct_uc}
    (SOME @{thm fixp_induct_error}) *}


  subsection \<open>Derived Definitions\<close>  

  definition "assert \<Phi> e \<equiv> if \<Phi> then return () else EAssert e"
  lemma assert_simps[simp]: 
    "assert True e = return ()"
    "assert False e = EAssert e"
    "assert \<Phi> e = return () \<longleftrightarrow> \<Phi>"
    unfolding assert_def by auto
    
  fun try_catch where  
    "try_catch (return m) _ = return m"
  | "try_catch (EAssert e) h = h e"
  | "try_catch ENonterm _ = ENonterm"  

  fun total_correct :: "('a,'e) error \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
    "total_correct (return v) \<Phi> = \<Phi> v" | "total_correct _ _ = False"

  fun terminating :: "('a,'e) error \<Rightarrow> bool" where
    "terminating ENonterm = False" | "terminating _ = True"

  fun partial_correct :: "('a,'e) error \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
    "partial_correct (return v) \<Phi> = \<Phi> v" 
  | "partial_correct (ENonterm) _ = True"
  | "partial_correct (EAssert _) _ = False"
    
  fun is_nonterm :: "('a,'e) error \<Rightarrow> bool" where
    "is_nonterm (ENonterm) = True"
  | "is_nonterm _ = False"  

  fun is_res :: "('a,'e) error \<Rightarrow> 'a \<Rightarrow> bool" where
    "is_res (return v) x \<longleftrightarrow> v=x"
  | "is_res _ _ \<longleftrightarrow> False"  

  fun is_error :: "('a,'e) error \<Rightarrow> 'e \<Rightarrow> bool" where
    "is_error (EAssert x) e \<longleftrightarrow> x=e"
  | "is_error _ _ \<longleftrightarrow> False"  

  lemma pw_nt_iff: "m=ENonterm \<longleftrightarrow> is_nonterm m" by (cases m) auto
  lemma pw_eq_iff: "m=m' 
    \<longleftrightarrow> (is_nonterm m = is_nonterm m') \<and> (\<forall>e. is_error m e \<longleftrightarrow> is_error m' e) \<and> (\<forall>x. is_res m x \<longleftrightarrow> is_res m' x)"
    by (cases m; cases m'; auto)
  lemma pw_err_iff: "m=EAssert e \<longleftrightarrow> is_error m e" by (cases m) auto 

  lemma 
    "total_correct m \<Phi> = (\<exists>x. is_res m x \<and> \<Phi> x)"
    "partial_correct m \<Phi> = total_correct m \<Phi> \<or> is_nonterm m"
    "terminating m \<longleftrightarrow> \<not>is_nonterm m"
    apply (cases m; simp)
    apply (cases "(m,\<Phi>)" rule: partial_correct.cases; simp)
    apply (cases m rule: terminating.cases; simp)
    done

  lemma pw_bind[simp]: 
    "is_res (m\<bind>f) x \<longleftrightarrow> (\<exists>y. is_res m y \<and> is_res (f y) x)"
    "is_nonterm (m\<bind>f) \<longleftrightarrow> is_nonterm m \<or> (\<exists>y. is_res m y \<and> is_nonterm (f y))"
    "is_error (m\<bind>f) e \<longleftrightarrow> is_error m e \<or> (\<exists>y. is_res m y \<and> is_error (f y) e)"
    by (cases m; simp; fail)+

  lemma pw_assert[simp]: 
    "is_res (assert \<Phi> msg) x \<longleftrightarrow> \<Phi>"
    "is_nonterm (assert \<Phi> msg) \<longleftrightarrow> False"
    "is_error (assert \<Phi> msg) e \<longleftrightarrow> \<not>\<Phi> \<and> msg=e"
    by (cases \<Phi>; simp; fail)+

  lemma pw_try_catch[simp]:
    "is_res (try_catch m h) x \<longleftrightarrow> is_res m x \<or> (\<exists>e. is_error m e \<and> is_res (h e) x)"  
    "is_nonterm (try_catch m h) \<longleftrightarrow> is_nonterm m \<or> (\<exists>e. is_error m e \<and> is_nonterm (h e))"
    "is_error (try_catch m h) e \<longleftrightarrow> (\<exists>e'. is_error m e' \<and> (is_error (h e') e))"
    by (cases m; auto; fail)+


  subsection \<open>Specifications\<close>  

  fun e_spec :: "('a \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> ('a,'e) error \<Rightarrow> bool" where 
    "e_spec P E T (return x) \<longleftrightarrow> P x"
  | "e_spec P E T (EAssert e) \<longleftrightarrow> E e"  
  | "e_spec P E T ENonterm \<longleftrightarrow> T"

  lemma pw_espec_iff: "e_spec P E T m \<longleftrightarrow> 
      (\<forall>x. is_res m x \<longrightarrow> P x)
    \<and> (\<forall>e. is_error m e \<longrightarrow> E e)
    \<and> (is_nonterm m \<longrightarrow> T)"
    by (cases m) auto

  (*abbreviation "et_spec' P E \<equiv> e_spec P E False" -- \<open>Total correctness, with error\<close>
  abbreviation "ep_spec' P E \<equiv> e_spec P E True" -- \<open>Partial correctness, with error\<close>

  abbreviation "et_spec P \<equiv> et_spec' P (\<lambda>_. False)"
  abbreviation "ep_spec P \<equiv> ep_spec' P (\<lambda>_. False)"
  *)

  subsection \<open>VCG\<close>

  named_theorems e_vcg \<open>VCG rules for error monad\<close>

  lemma e_cons: "\<lbrakk>e_spec P E T m; \<And>x. P x \<Longrightarrow> P' x; \<And>e. E e \<Longrightarrow> E' e; T \<Longrightarrow> T' \<rbrakk> 
    \<Longrightarrow> e_spec P' E' T' m"
    by (auto simp: pw_espec_iff)
   


  lemma e_vcg_basic[e_vcg]:
    "P x \<Longrightarrow> e_spec P E T (return x)"
    "E e \<Longrightarrow> e_spec P E T (EAssert e)"
    "T \<Longrightarrow> e_spec P E T (ENonterm)"
    by auto

  lemma (in -) e_Let_vcg[e_vcg]: "e_spec P E T (f v) \<Longrightarrow> e_spec P E T (let x=v in f x)" by simp

  lemma e_bind_vcg[e_vcg]:
    assumes "e_spec (\<lambda>x. e_spec P E T (f x)) E T m"
    shows "e_spec P E T (do { x \<leftarrow> m; f x })"  
    using assms
    by (auto simp: pw_espec_iff)

  lemma e_assert_vcg[e_vcg]:
    "\<lbrakk> \<Phi> \<Longrightarrow> P (); \<not>\<Phi> \<Longrightarrow> E e \<rbrakk> \<Longrightarrow> e_spec P E T (assert \<Phi> e)"  
    by (auto simp: pw_espec_iff)
    
  lemma e_try_catch[e_vcg]:
    assumes "e_spec P E' T m"
    assumes "\<And>e. E' e \<Longrightarrow> e_spec P E T (h e)"
    shows "e_spec P E T (try_catch m h)"  
    using assms
    by (auto simp: pw_espec_iff)


  lemma split_rule_unfolds:
    "Trueprop (a\<longrightarrow>b) \<equiv> (a\<Longrightarrow>b)"  
    "(a \<and> b \<Longrightarrow> PROP Q) \<equiv> (\<lbrakk>a;b\<rbrakk>\<Longrightarrow>PROP Q)"
    "Trueprop (\<forall>x. p x) \<equiv> (\<And>x. p x)"
    apply presburger
    apply (rule conj_imp_eq_imp_imp)
    by presburger
    
  (* TODO: Automate generation of split rules *)  
  lemmas prod_split_e_vcg[e_vcg] = prod.split[where P="e_spec P E T" for P E T, THEN iffD2, unfolded split_rule_unfolds]
  lemmas option_split_e_vcg[e_vcg] = option.split[where P="e_spec P E T" for P E T, THEN iffD2, unfolded split_rule_unfolds]

  lemmas (in -) e_if_vcg[e_vcg] = 
    split_if[where P="e_spec P E T" for P E T, THEN iffD2, unfolded split_rule_unfolds]

  lemma is_espec_rl: "e_spec P E T m \<Longrightarrow> e_spec P E T m" .

  ML \<open>
    structure e_vcg = struct  

      val vcg_modifiers = [
        Args.$$$ "vcg" -- Scan.option Args.add -- Args.colon 
          >> K (Method.modifier (Named_Theorems.add @{named_theorems e_vcg}) @{here}),
        Args.$$$ "vcg" -- Scan.option Args.del -- Args.colon 
          >> K (Method.modifier (Named_Theorems.del @{named_theorems e_vcg}) @{here})
      ];

      val e_vcg_modifiers = 
        clasimp_modifiers @ vcg_modifiers;

      fun e_vcg try_solve ctxt = let
  
        val ps_ctxt = Splitter.del_split @{thm split_if} ctxt
  
        val vcg_thms = Named_Theorems.get ctxt @{named_theorems e_vcg}
  
        fun TRY_SOLVE tac = SOLVED' tac ORELSE' (DETERM o tac)
  
        val vcg_rule_tac = resolve_tac ctxt @{thms is_espec_rl}
          THEN' (
            rprems_tac ctxt ORELSE' resolve_tac ctxt vcg_thms
          )
  
        val vcg_step_tac = 
          vcg_rule_tac
          ORELSE'
          (resolve_tac ctxt @{thms e_cons} THEN' vcg_rule_tac)
  
        val solve_other_tac = 
          TRY o (SOLVED' (SELECT_GOAL (auto_tac ctxt)))
  
        fun tac i = (
          Method.assm_tac ctxt
          ORELSE' (clarsimp_tac ps_ctxt THEN_ALL_NEW TRY_SOLVE ( vcg_step_tac THEN_ALL_NEW_FWD tac ))
          ORELSE' solve_other_tac
        ) i
  
        val tac' = REPEAT_ALL_NEW_FWD (FIRST' [Method.assm_tac ctxt,clarsimp_tac ps_ctxt THEN_ALL_NEW_FWD vcg_step_tac])
  
      in
        if try_solve then tac else tac' 
      end 


      fun gen_e_vcg_method try_solve = 
        Method.sections e_vcg_modifiers >> (fn _ => fn ctxt => 
          SIMPLE_METHOD' (CHANGED o e_vcg try_solve ctxt))

    end  
  \<close>

  method_setup e_vcg = \<open>e_vcg.gen_e_vcg_method true\<close> \<open>VCG for the error monad (with auto-solver)\<close>
  method_setup e_vcg' = \<open>e_vcg.gen_e_vcg_method false\<close> \<open>VCG for the error monad (no solvers)\<close>





  subsection \<open>Standard Combinators\<close>

  primrec emap :: "('a \<Rightarrow> ('b,'e)error) \<Rightarrow> 'a list \<Rightarrow> ('b list,'e) error" where
    "emap _ [] = return []"
  | "emap f (x#xs) = do {
      y \<leftarrow> f x;
      ys \<leftarrow> emap f xs;
      return (y#ys)
    }"
  
  lemma emap_cong[fundef_cong]: "\<lbrakk> xs = ys; \<And>x. x\<in>set ys \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> emap f xs = emap g ys"
    apply (induction ys arbitrary: xs)
    apply (auto split: Error_Monad.bind_split)
    done

  primrec efold :: "('a \<Rightarrow> 's \<Rightarrow> ('s,'e) error) \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> ('s,'e) error" where
    "efold f [] s = return s"
  | "efold f (x#xs) s = do {
      s \<leftarrow> f x s;
      efold f xs s
    }"  

  lemma efold_cong[fundef_cong]: "\<lbrakk>a=b; xs=ys; \<And>x. x\<in>set ys \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> efold f xs a = efold g ys b"
    by (induction xs arbitrary: ys a b) (auto split: Error_Monad.bind_splits)


  thm partial_function_mono  
  lemma efold_mono[partial_function_mono]:     
  fixes f :: "('c \<Rightarrow> ('d, 'e) error) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('b, 'e) error"
  assumes [partial_function_mono]: "\<And>x \<sigma>. mono_error (\<lambda>fa. f fa x \<sigma>)"
  shows "mono_error (\<lambda>x. efold (f x) l \<sigma>)"
    apply (induction l arbitrary: \<sigma>)
    apply simp
    apply (tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
    apply simp
    apply (rule bind_mono)
    apply (tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
    .


  definition elookup :: "('k \<Rightarrow> 'e) \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> 'k \<Rightarrow> ('v,'e) error" where
    "elookup E m k \<equiv> case m k of None \<Rightarrow> EAssert (E k) | Some v \<Rightarrow> return v"

  subsection \<open>Regression Test\<close>  
  context begin  

  private partial_function (error) foo :: "nat \<Rightarrow> (nat,string) error" where
    "foo i = (case i of 0 \<Rightarrow> return 1 | (Suc n) \<Rightarrow> do {
      m \<leftarrow> foo n;
      return (Suc m)
    })"  

  end


end
