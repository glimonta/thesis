theory SmallStep
imports
  "~~/src/HOL/IMP/Star"
  "~~/src/HOL/Library/While_Combinator"
  Eval
begin


(*
fun update_locs :: "vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "update_locs x a (\<sigma>, \<gamma>, \<mu>) = (\<sigma>(x:=Some a), \<gamma>, \<mu>)"*)

type_synonym enabled = "state \<rightharpoonup> bool"
type_synonym transformer = "state \<rightharpoonup> state"
type_synonym cfg_label = "enabled \<times> transformer"

locale program =
  fixes program :: program
  assumes valid: "valid_program proc_table"
begin
  definition "proc_table == proc_table_of program"
end

abbreviation en_always :: enabled where "en_always \<equiv> \<lambda>_. Some True"
abbreviation (input) tr_id :: transformer where "tr_id \<equiv> Some"

definition "tr_assign x a \<equiv> lift_transformer_nr (\<lambda>s. do {
  (v,s) \<leftarrow> eval a s;
  s \<leftarrow> write_var x v s;
  Some s
})"

definition tr_assignl :: "lexp \<Rightarrow> exp \<Rightarrow> transformer"
where "tr_assignl x a \<equiv> lift_transformer_nr (\<lambda>s. do {
  (addr,s) \<leftarrow> eval_l x s;
  (v,s) \<leftarrow> eval a s;
  store addr v s
})"

fun truth_value_of :: "val \<Rightarrow> bool" where
  "truth_value_of NullVal \<longleftrightarrow> False"
| "truth_value_of (I i) \<longleftrightarrow> i\<noteq>0"
| "truth_value_of (A _) \<longleftrightarrow> True"

definition en_pos :: "exp \<Rightarrow> enabled" where
  "en_pos e s \<equiv> do {
    (v,_) \<leftarrow> lift_transformer (eval e) s;
    let b = truth_value_of v;
    Some b
  }"

definition en_neg :: "exp \<Rightarrow> enabled" where
  "en_neg e s \<equiv> do {
    (v,_) \<leftarrow> lift_transformer (eval e) s;
    let b = truth_value_of v;
    Some (\<not>b)
  }"

definition tr_eval :: "exp \<Rightarrow> transformer" where
  "tr_eval e \<equiv> lift_transformer_nr (\<lambda>s. do {
    (_,s) \<leftarrow> eval e s;
    Some s
  })"

definition tr_free :: "lexp \<Rightarrow> transformer" where
  "tr_free e \<equiv> lift_transformer_nr (\<lambda>s. do {
    (addr, s) \<leftarrow> eval_l e s;
    s \<leftarrow> free addr s;
    Some s
  })"

fun real_values :: "exp list \<Rightarrow> visible_state \<Rightarrow> (val list \<times> visible_state) option" where
  "real_values [] s = Some ([], s)"
| "real_values (x#xs) s = do {
    (v,s) \<leftarrow> eval x s;
    (vals, s) \<leftarrow> real_values xs s;
    Some ([v] @ vals, s)
  }"

context fixes program :: program begin

  private definition "proc_table \<equiv> proc_table_of program"

  definition "main_decl \<equiv> the (proc_table ''main'')"
  definition "main_local_names \<equiv> fun_decl.locals main_decl"
  definition "main_com \<equiv> fun_decl.body main_decl"

  definition initial_stack :: "stack_frame list" where
    "initial_stack \<equiv> [(main_com,map_of (map (\<lambda>x. (x,None)) main_local_names),Invalid)]"
  definition initial_glob :: valuation where 
    "initial_glob \<equiv> map_of (map (\<lambda>x. (x,None)) (program.globals program))"
  (*definition initial_proc :: proc_table where "initial_proc \<equiv> \<lambda>name. None" *)
  definition initial_mem :: mem where "initial_mem \<equiv> []"
  definition initial_state :: state 
    where "initial_state \<equiv> (initial_stack, initial_glob, initial_mem)"

end

value (code) "lift_transformer 
  (real_values [(Const 1), (Plus (Const 1) (Const 2))]) (initial_state p)"

(* A function can be called if the number of parameters from the function and the actual parameters
   used when calling it match, otherwise it can't be called 
   If the number of parameters is wrong we return None instead of False because we want it to stop
   executing \<rightarrow> it's an error. *)
(*definition en_callfun :: "fname \<Rightarrow> exp list \<Rightarrow> enabled" where
  "en_callfun f values _ \<equiv> do {
    (params, locals, _) \<leftarrow> proc_table f;
    if (list_size params) = (list_size values) then Some True else None
  }"*)


fun push_stack :: "stack_frame \<Rightarrow> transformer" where
  "push_stack sf (\<sigma>,\<gamma>,\<mu>) = Some (sf#\<sigma>,\<gamma>,\<mu>)"

fun pop_stack :: "transformer" where
  "pop_stack (sf#\<sigma>,\<gamma>,\<mu>) = Some (\<sigma>,\<gamma>,\<mu>)"
| "pop_stack _ = None"

fun top_stack :: "state \<Rightarrow> stack_frame option" where
  "top_stack (sf#\<sigma>,_,_) = Some sf"
| "top_stack _ = None"


definition call_function :: "proc_table \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer"
where "call_function proc_table f params_exp s \<equiv> do {
  fdecl \<leftarrow> proc_table f;
  assert (length params_exp = length (fun_decl.params fdecl));
  (params_val, s) \<leftarrow> lift_transformer (real_values params_exp) s;
  let locals = 
     map_of (zip (fun_decl.params fdecl) (map Some params_val)) 
  ++ map_of (map (\<lambda>x. (x,None)) (fun_decl.locals fdecl));
  let sf = ((fun_decl.body fdecl),locals,Invalid);
  push_stack sf s
}"

definition set_rloc :: "return_loc \<Rightarrow> transformer" where
  "set_rloc rloc \<equiv> \<lambda>((com,locals,_)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> 
    Some ((com,locals,rloc)#\<sigma>,\<gamma>,\<mu>)
  "

definition get_rloc :: "state \<Rightarrow> return_loc" where
  "get_rloc \<equiv> \<lambda>((com,locals,rloc)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> rloc"


definition tr_callfunl :: "proc_table \<Rightarrow> lexp \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer" where
  "tr_callfunl proc_table x f args s \<equiv> do {
    (addr,s) \<leftarrow> lift_transformer (eval_l x) s;
    s \<leftarrow> set_rloc (Ar addr) s;
    call_function proc_table f args s
  }"

definition tr_callfun :: "proc_table \<Rightarrow> vname \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer" where
  "tr_callfun proc_table x f args s \<equiv> do {
    s \<leftarrow> set_rloc (Vr x) s;
    call_function proc_table f args s
  }"


(* Return eliminates the returning function's stack_frame, then assigns the result to the variable 
   or address where it's supposed to be assigned *)
definition tr_return :: "exp \<Rightarrow> transformer" where
  "tr_return a s = do {
    (v,s) \<leftarrow> lift_transformer (eval a) s;
    s \<leftarrow> pop_stack s;
    if \<not>is_empty_stack s then
      case get_rloc s of
        Ar addr \<Rightarrow> lift_transformer_nr (store addr v) s
      | Vr x \<Rightarrow> lift_transformer_nr (write_var x v) s
      | Invalid \<Rightarrow> Some s
    else
      Some s
  }"
    
definition tr_return_void :: "transformer" where
  "tr_return_void s = do {
    s \<leftarrow> pop_stack s;
    if \<not>is_empty_stack s then
      case get_rloc s of
        Ar addr \<Rightarrow> None
      | Vr x \<Rightarrow> None
      | Invalid \<Rightarrow> Some s
    else
      Some s
  }"

context program begin

inductive cfg :: "com \<Rightarrow> cfg_label \<Rightarrow> com \<Rightarrow> bool" where
  Assign: "cfg (x ::= a) (en_always,tr_assign x a) SKIP"
| Assignl: "cfg (x ::== a) (en_always,tr_assignl x a) SKIP"
| Seq1: "cfg (SKIP;; c\<^sub>2) (en_always, tr_id) c\<^sub>2"
| Seq2: "\<lbrakk>cfg c\<^sub>1 a c\<^sub>1'\<rbrakk> \<Longrightarrow> cfg (c\<^sub>1;; c\<^sub>2) a (c\<^sub>1';; c\<^sub>2)"
| IfTrue: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (en_pos b, tr_eval b) c\<^sub>1"
| IfFalse: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (en_neg b, tr_eval b) c\<^sub>2"
| While: "cfg (WHILE b DO c) (en_always, tr_id) (IF b THEN c;; WHILE b DO c ELSE SKIP)"
| Free: "cfg (FREE x) (en_always, tr_free x) SKIP"

| Return: "cfg (Return a) (en_always, tr_return a) SKIP"

| Callfunl: "cfg (Callfunl e f params) (en_always, tr_callfunl proc_table e f params) SKIP"
| Callfun: "cfg (Callfun x f params) (en_always, tr_callfun proc_table x f params) SKIP"

(* A configuration can take a small step if there's a cfg edge between the two commands, the
   enabled returns True and the transformer successfully transforms the state into a new one.
   If the enabled does not allow for the execution to continue then it goes to None, same
   thing happens if the enabled or the transformer return None as a result.
  *)
inductive 
  small_step :: "state \<Rightarrow> state option \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
  Base: "\<lbrakk> \<not>is_empty_stack s; c\<^sub>1=com_of s; cfg c\<^sub>1 (en, tr) c\<^sub>2; en s = Some True; tr (upd_com c\<^sub>2 s) = Some s\<^sub>2\<rbrakk> \<Longrightarrow> s \<rightarrow> Some s\<^sub>2"
| None: "\<lbrakk> \<not>is_empty_stack s; c\<^sub>1=com_of s; cfg c\<^sub>1 (en, tr) c\<^sub>2; en s = None     \<or> tr (upd_com c\<^sub>2 s) = None\<rbrakk> \<Longrightarrow>    s \<rightarrow> None"
| Return_void: "\<lbrakk> \<not>is_empty_stack s; com_of s = SKIP; tr_return_void s = Some s' \<rbrakk> \<Longrightarrow> s \<rightarrow> Some s'"
| Return_void_None: "\<lbrakk> \<not>is_empty_stack s; com_of s = SKIP; tr_return_void s = None \<rbrakk> \<Longrightarrow> s \<rightarrow> None"

inductive
  small_step' :: "(state) option \<Rightarrow> (state) option \<Rightarrow> bool" (infix "\<rightarrow>' " 55)
where
  "cs \<rightarrow> cs' \<Longrightarrow> Some cs \<rightarrow>' cs'"

abbreviation
  small_steps :: "(state) option \<Rightarrow> (state) option \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step' x y"

(** A sanity check. I'm trying to prove that the semantics
  only gets stuck at SKIP. This may reveal some problems in your
  current semantics: **)

(*lemma
  assumes "c\<noteq>SKIP"
  shows "\<exists>x. (c,s) \<rightarrow> x"
  using assms apply (induction c)
  apply (auto intro: small_step.intros cfg.intros)
apply (metis Assignl Base not_None_eq small_step.intros(2))
apply (metis Assign Base not_None_eq small_step.intros(2))
  *)

lemma cfg_has_enabled_action:
  assumes "c\<noteq>SKIP"
  shows "\<exists>c' en tr. cfg c (en,tr) c' \<and> (en s = None \<or> en s = Some True)" 
  using assms
proof (induction c)
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "c\<^sub>1 = SKIP")
    case True
    thus ?thesis by (auto intro: cfg.intros)
  next
    case False
    from Seq.IH(1)[OF this] show ?thesis by (auto intro: cfg.intros)
  qed  
next
  case (If b c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "en_pos b s")
    case None[simp]
    thus ?thesis by (fastforce intro: cfg.intros)
  next
    case (Some a)[simp]
      show ?thesis
      proof (cases a)
        case True
        thus ?thesis by (fastforce intro: cfg.intros)
      next
        case False[simp]
        have "en_pos b s = Some False" by simp
        hence "en_neg b s = Some True"
          unfolding en_pos_def en_neg_def
          by (auto split: Option.bind_splits)
        thus ?thesis by (fastforce intro: cfg.intros)
      qed
  qed
qed (auto intro: cfg.intros)

(*lemma cfg_preserves_def_returns:
  assumes "cfg c a c'"
  assumes "def_returns c"
  shows "def_returns c' \<or> (\<exists>e. a=(en_always,tr_return e))"
  using assms
  apply induction
  apply auto
  done

definition "def_returns_com_stack s \<equiv> \<forall>com\<in>coms_of_state s. def_returns com"
*)

lemma assert_simps[simp]:
  "assert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"
  "assert \<Phi> = Some () \<longleftrightarrow> \<Phi>"
  unfolding assert_def by auto


lemma aux:
  assumes [simp, intro!]: "\<not>is_empty_stack s"
  shows "\<exists>x. s \<rightarrow> x"
  using assms
proof -
  from assms obtain c locals rloc \<sigma> \<gamma> \<mu> where 
    [simp]: "s = ((c,locals,rloc)#\<sigma>, \<gamma>,\<mu>)"
    unfolding is_empty_stack_def
    apply (simp add: neq_Nil_conv split: prod.splits)
    by auto
    
  show ?thesis proof (cases "c=SKIP")
    case True[simp]
    show ?thesis apply auto
      by (metis Base None Return_void Return_void_None True 
        `s = ((c, locals, rloc) # \<sigma>, \<gamma>, \<mu>)` assms cfg_has_enabled_action 
        option.exhaust)
  next    
    case False
    from cfg_has_enabled_action[OF False] obtain c' en tr 
      where "cfg c (en, tr) c' \<and> (en s = None \<or> en s = Some True)" by blast
    thus ?thesis proof safe
      assume "cfg c (en, tr) c'" "en s = None"
      thus ?thesis apply - apply (rule exI) apply (rule small_step.None)
      by auto
    next  
      assume A: "cfg c (en, tr) c'" "en s = Some True"
      thus ?thesis proof (cases "tr (upd_com c' s)")
        case None with A show ?thesis 
          by (force intro: small_step.None)
      next    
        case Some with A show ?thesis 
          by (force intro: small_step.Base)
      qed
    qed 
  qed
qed 

lemma cfg_SKIP_stuck[simp]: "\<not> cfg SKIP a c"
  by (auto elim: cfg.cases)

lemma ss_empty_stack_stuck[simp]: "is_empty_stack s \<Longrightarrow> \<not>( s \<rightarrow> cs')"
  by (auto elim: small_step.cases)

lemma ss'_SKIP_stuck[simp]: "is_empty_stack s \<Longrightarrow> \<not>( Some s \<rightarrow>' cs')"
  by (auto elim: small_step'.cases)


lemma en_neg_by_pos: "en_neg e s = map_option (HOL.Not) (en_pos e s)"
  unfolding en_pos_def en_neg_def
  by (auto split: Option.bind_splits)

lemma cfg_determ:
  assumes "cfg c a1 c'"
  assumes "cfg c a2 c''"
  obtains
      "a1=a2" "c' = c''"
    | b where "a1 = (en_pos b,tr_eval b)" "a2 = (en_neg b,tr_eval b)"
    | b where "a1 = (en_neg b,tr_eval b)" "a2 = (en_pos b,tr_eval b)"
  using assms
  apply (induction arbitrary: c'')
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (rotate_tac)
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (rotate_tac)
  apply (erule cfg.cases, auto) []
  apply (rotate_tac)
  apply (erule cfg.cases, auto) []
  done

lemma lift_upd_com: "\<not>is_empty_stack s \<Longrightarrow>
  lift_transformer_nr tr (upd_com c s) = 
  map_option (upd_com c) (lift_transformer_nr tr s)"
  unfolding lift_transformer_nr_def
  by (auto split: prod.splits list.splits Option.bind_split)

lemma tr_eval_upd_com: "\<not>is_empty_stack s \<Longrightarrow> 
  tr_eval e (upd_com c s) = map_option (upd_com c) (tr_eval e s)"
  unfolding tr_eval_def
  by (auto simp: lift_upd_com)

lemma small_step_determ:
  assumes "s \<rightarrow> s'"
  assumes "s \<rightarrow> s''"
  shows "s'=s''"
  using assms
  apply (cases)
  apply (erule small_step.cases)
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos tr_eval_upd_com) []
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos tr_eval_upd_com) []
  apply simp
  apply simp

  apply (erule small_step.cases)
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos tr_eval_upd_com) []
  apply simp
  apply simp
  apply simp

  apply (erule small_step.cases)
  apply simp
  apply simp
  apply simp
  apply simp

  apply (erule small_step.cases)
  apply simp
  apply simp
  apply simp
  apply simp
  done

end

datatype cfg_edge = Base transformer com | Cond enabled transformer com com

context fixes proc_table :: proc_table begin

fun cfg_step :: "com \<Rightarrow> cfg_edge" where
  "cfg_step SKIP = undefined"
| "cfg_step (x ::= a) = Base (tr_assign x a) SKIP"
| "cfg_step (x ::== a) = Base (tr_assignl x a) SKIP"
| "cfg_step (SKIP;; c2) = Base tr_id c2"
| "cfg_step (c1;;c2) = (case cfg_step c1 of
    Base tr c \<Rightarrow> Base tr (c;;c2)
  | Cond en tr ca cb \<Rightarrow> Cond en tr (ca;;c2) (cb;;c2)  
   )"
| "cfg_step (IF b THEN c1 ELSE c2) = Cond (en_pos b) (tr_eval b) c1 c2"
| "cfg_step (WHILE b DO c) = Base tr_id (IF b THEN c;; WHILE b DO c ELSE SKIP)"
| "cfg_step (FREE x) = Base (tr_free x) SKIP"
| "cfg_step (Return a) = Base (tr_return a) SKIP"
| "cfg_step (Callfunl e f params) = Base (tr_callfunl proc_table e f params) SKIP"
| "cfg_step (Callfun x f params) = Base (tr_callfun proc_table x f params) SKIP"

end

context program begin

  lemma step_to_cfg_base: "c \<noteq> SKIP \<Longrightarrow> (cfg_step proc_table c = Base tr c') \<Longrightarrow> cfg c (en_always,tr) c'"
    apply (induction c arbitrary: tr c' rule: cfg_step.induct)
    apply (auto intro: cfg.intros elim: cfg.cases split: cfg_edge.splits)
    done

  lemma step_to_cfg_cond: "c \<noteq> SKIP \<Longrightarrow> (cfg_step proc_table c = Cond en tr c1' c2') \<Longrightarrow>
    (cfg c (en,tr) c1' \<or> cfg c (map_option HOL.Not o en, tr) c2' )"
    apply (induction c arbitrary: tr c1' c2' rule: cfg_step.induct)
    apply (auto 
      intro: cfg.intros elim: cfg.cases split: cfg_edge.splits simp: en_neg_by_pos)
    apply (force intro: cfg.intros)
    done

  lemma cfg_to_stepE:
    assumes "cfg c a c'"  
    assumes "c\<noteq>SKIP"
    obtains 
      tr where "a = (en_always, tr)" "cfg_step proc_table c = Base tr c'"
    | b c2' where "a = (en_pos b, tr_eval b)" "cfg_step proc_table c = Cond (en_pos b) (tr_eval b) c' c2'"
    | b c1' where "a = (en_neg b, tr_eval b)" "cfg_step proc_table c = Cond (en_pos b) (tr_eval b) c1' c'"
    using assms
    apply (induction)    
    apply auto
    apply (case_tac "c\<^sub>1")
    apply auto
    done
    
end


definition fstep :: "proc_table \<Rightarrow> state \<Rightarrow> state option" where
  "fstep proc_table s \<equiv> 
    if com_of s = SKIP then
      tr_return_void s
    else
      case cfg_step proc_table (com_of s) of
          Base tr c' \<Rightarrow> tr (upd_com c' s)
        | Cond en tr c1 c2 \<Rightarrow> do {
            b \<leftarrow> en s;
            if b then
              tr (upd_com c1 s)
            else  
              tr (upd_com c2 s)
          }"

context program begin

  lemma fstep1: 
    assumes "s \<rightarrow> s'"  
    shows "fstep proc_table s = s'"
    using assms
    apply cases
    apply (auto simp: fstep_def)

    apply (erule cfg_to_stepE)
    apply (auto split: Option.bind_split simp: en_neg_by_pos)
    
    apply (erule cfg_to_stepE)
    apply (auto split: Option.bind_split simp: en_neg_by_pos)

    apply (erule cfg_to_stepE)
    apply (auto split: Option.bind_split simp: en_neg_by_pos tr_eval_upd_com)
    done
    

lemma fstep2: "\<not>is_empty_stack s \<Longrightarrow> s \<rightarrow> (fstep proc_table s)"
  unfolding fstep_def
  apply simp apply safe
  apply (cases "tr_return_void s")
  apply (auto intro: small_step.intros) [2]

  apply (simp split: cfg_edge.splits, safe)
  apply (frule (1) step_to_cfg_base)
  apply (metis (no_types, lifting) aux cfg_edge.simps(5) fstep1 fstep_def)
  apply (frule (1) step_to_cfg_cond)
  apply (auto split: Option.bind_splits intro: small_step.intros)
  apply (metis (mono_tags, lifting) aux bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  apply (metis (mono_tags, lifting) aux bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  apply (metis (mono_tags, lifting) aux bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  apply (metis (mono_tags, lifting) aux bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  done  
  
end
  
fun is_term :: "state option \<Rightarrow> bool" where
  "is_term (Some s) = is_empty_stack s"
| "is_term None = True"


definition interp :: "proc_table \<Rightarrow> state \<Rightarrow> state option" where
  "interp proc_table cs \<equiv> (while
    (HOL.Not o is_term)
    (\<lambda>Some cs \<Rightarrow> fstep proc_table cs)
    (Some cs))"

lemma interp_unfold: "interp proc_table cs = (
    if is_term (Some cs) then
      Some cs
    else do {
      cs \<leftarrow> fstep proc_table cs;
      interp proc_table cs
    }
  )"
  unfolding interp_def
  apply (subst while_unfold)
  apply (auto split: Option.bind_split)
  apply (subst while_unfold)
  apply auto
  done


lemma interp_term: "is_term (Some cs) \<Longrightarrow> interp proc_table cs = Some cs"
  apply (subst interp_unfold)
  by simp

context program begin
  definition "yields == \<lambda>cs cs'. Some cs \<rightarrow>* cs' \<and> is_term cs'"
  definition "terminates == \<lambda>cs. \<exists>cs'. yields cs cs'"

  lemma None_star_preserved[simp]: "None \<rightarrow>* z \<longleftrightarrow> z=None"
  proof
    assume "None \<rightarrow>* z"
    thus "z=None"
      apply (induction "None::(state) option" z rule: star.induct)
      apply (auto elim: small_step'.cases)
      done
  qed auto

  lemma small_step'_determ:
    assumes "c \<rightarrow>' c1"
    assumes "c \<rightarrow>' c2"
    shows "c1=c2"
    using assms(1)
    apply cases
    using assms(2)
    apply (cases)
    apply (auto simp: small_step_determ)
    done

  theorem interp_correct:
    assumes TERM: "terminates cs"
    shows "(yields cs cs') \<longleftrightarrow> (cs' = interp proc_table cs)"
  proof safe
    assume "yields cs cs'"
    hence a: "Some cs \<rightarrow>* cs'" and b: "is_term cs'" unfolding yields_def by auto
    thus "cs' = interp proc_table cs"
    proof (induction _ "Some cs" _ arbitrary: cs rule: star.induct)
      case refl with interp_term show ?case by simp
    next
      case (step csh cs')
      from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "fstep proc_table cs = csh"
        apply (cases)
        apply (cases cs, cases csh)
        apply (auto intro: fstep1)
        done
  
      from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_term (Some cs)" 
        apply (cases "Some cs" rule: is_term.cases)
        by auto
  
      from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_empty_stack cs" 
        apply (cases "Some cs" rule: is_term.cases)
        by auto

      show ?case
      proof (cases csh)
        case None[simp]
  
        from \<open>csh \<rightarrow>* cs'\<close> have [simp]: "cs'=None" by simp
  
        show ?thesis
          by (subst interp_unfold) auto

      next
        case (Some cst)[simp]
  
        have "interp proc_table cs = interp proc_table cst"
          by (subst interp_unfold) simp
        thus ?thesis using step.hyps(3)[OF Some step.prems]
          by simp
      qed
    qed
  next
    from TERM obtain cs' where
      1: "Some cs \<rightarrow>* cs'" "is_term cs'"
      unfolding yields_def terminates_def by auto
    hence "cs'=interp proc_table cs"
    proof (induction "Some cs" _ arbitrary: cs rule: star.induct)
      case refl thus ?case by (simp add: interp_term)
    next
      case (step csh cs')
  
      from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "fstep proc_table cs = csh"
        apply (cases)
        apply (cases cs, cases csh)
        apply (auto intro: fstep1)
        done
  
      from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_term (Some cs)"
        apply (cases "Some cs" rule: is_term.cases)
        by auto

      from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_empty_stack cs"
        apply (cases "Some cs" rule: is_term.cases)
        by auto
  
      show ?case
      proof (cases csh)
        case None[simp]
  
        from \<open>csh \<rightarrow>* cs'\<close> have [simp]: "cs'=None" by simp
  
        show ?thesis
          by (subst interp_unfold) simp
      next
        case (Some cst)[simp]
  
        have "interp proc_table cs = interp proc_table cst"
          by (subst interp_unfold) simp
        thus ?thesis using step.hyps(3)[OF Some step.prems]
          by simp
      qed
    qed
    with 1 have "Some cs \<rightarrow>* interp proc_table cs" "is_term (interp proc_table cs)" by simp_all
    thus "yields cs (interp proc_table cs)" by (auto simp: yields_def)
  qed
  
  
  

lemmas [code] = interp_unfold

export_code interp checking SML


end


definition execute :: "program \<Rightarrow> state option" where
  "execute p \<equiv> do {
    assert (valid_program p);
    interp (proc_table_of p) (initial_state p)
  }"

export_code execute checking SML


end

