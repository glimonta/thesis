theory SmallStep
imports
  Eval
  "~~/src/HOL/IMP/Star"
  "~~/src/HOL/Library/While_Combinator"
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Code_Target_Int"
  "~~/src/HOL/Library/Code_Target_Nat"
begin

  (* TODO: Should be contained in Isabelle since de0a4a76d7aa under
    Option.bind_split{s,_asm}*)
  lemma option_bind_split: "P (Option.bind m f)
  \<longleftrightarrow> (m = None \<longrightarrow> P None) \<and> (\<forall>v. m=Some v \<longrightarrow> P (f v))"
    by (cases m) auto

  lemma option_bind_split_asm: "P (Option.bind m f) = (\<not>(
      m=None \<and> \<not>P None
    \<or> (\<exists>x. m=Some x \<and> \<not>P (f x))))"
    by (cases m) auto

  lemmas option_bind_splits = option_bind_split option_bind_split_asm

(*
fun update_locs :: "vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "update_locs x a (\<sigma>, \<gamma>, \<mu>) = (\<sigma>(x:=Some a), \<gamma>, \<mu>)"*)

type_synonym enabled = "state \<rightharpoonup> bool"
type_synonym transformer = "state \<rightharpoonup> state"
type_synonym cfg_label = "enabled \<times> transformer"

locale program = 
  fixes proc_table :: "program"
  assumes "valid_program proc_table"
begin

abbreviation en_always :: enabled where "en_always \<equiv> \<lambda>_. Some True"
abbreviation (input) tr_id :: transformer where "tr_id \<equiv> Some"

definition "tr_assign x a s \<equiv> do {
  (v,s) \<leftarrow> eval a s;
  s \<leftarrow> write_var x v s;
  Some s
}"

definition tr_assignl :: "lexp \<Rightarrow> exp \<Rightarrow> transformer"
where "tr_assignl x a s \<equiv> do {
  (addr,s) \<leftarrow> eval_l x s;
  (v,s) \<leftarrow> eval a s;
  store addr v s
}"

fun truth_value_of :: "val \<Rightarrow> bool" where
  "truth_value_of NullVal \<longleftrightarrow> False"
| "truth_value_of (I i) \<longleftrightarrow> i\<noteq>0"
| "truth_value_of (A _) \<longleftrightarrow> True"

definition en_pos :: "exp \<Rightarrow> enabled" where
  "en_pos e s \<equiv> do {
    (v,_) \<leftarrow> eval e s;
    let b = truth_value_of v;
    Some b
  }"

definition en_neg :: "exp \<Rightarrow> enabled" where
  "en_neg e s \<equiv> do {
    (v,_) \<leftarrow> eval e s;
    let b = truth_value_of v;
    Some (\<not>b)
  }"

definition tr_eval :: "exp \<Rightarrow> transformer" where
  "tr_eval e s \<equiv> do {
    (_,s) \<leftarrow> eval e s;
    Some s
  }"

definition tr_free :: "lexp \<Rightarrow> transformer" where
  "tr_free e s \<equiv> do {
    (addr, (\<sigma>, \<gamma>, \<mu>)) \<leftarrow> eval_l e s;
    \<mu> \<leftarrow> free addr \<mu>;
    Some (\<sigma>, \<gamma>, \<mu>)
  }"

(* Takes the actual values list, the parameter names list and returns the valuation new stack_frame
   if it returns none it's because the lists had different length \<Rightarrow> error *)
fun create_locals_stack_frame :: "vname list \<Rightarrow> val list \<Rightarrow> valuation option" where
  "create_locals_stack_frame [] [] = Some (\<lambda>name. None)"
| "create_locals_stack_frame (x#xs) [] =  do {
    sf \<leftarrow> (create_locals_stack_frame xs []);
    Some (sf (x \<mapsto> None))
  }"
| "create_locals_stack_frame (x#xs) (y#ys) = do {
    sf \<leftarrow> (create_locals_stack_frame xs ys);
    Some (sf (x \<mapsto> Some y))
  }"
| "create_locals_stack_frame _ _ = None"
  

fun real_values :: "exp list \<Rightarrow> state \<Rightarrow> (val list \<times> state) option" where
  "real_values [] s = Some ([], s)"
| "real_values (x#xs) s = do {
    (v,s) \<leftarrow> eval x s;
    (vals, s) \<leftarrow> real_values xs s;
    Some ([v] @ vals, s)
  }"

definition initial_stack :: "stack_frame list" where "initial_stack \<equiv> []"
definition initial_glob :: valuation where "initial_glob \<equiv> \<lambda>name. None"
(*definition initial_proc :: proc_table where "initial_proc \<equiv> \<lambda>name. None" *)
definition initial_mem :: mem where "initial_mem \<equiv> []"
definition initial_state :: state 
  where "initial_state \<equiv> (initial_stack, initial_glob, initial_mem)"

value "real_values [(Const 1), (Plus (Const 1) (Const 2))] initial_state"

(* A function can be called if the number of parameters from the function and the actual parameters
   used when calling it match, otherwise it can't be called 
   If the number of parameters is wrong we return None instead of False because we want it to stop
   executing \<rightarrow> it's an error. *)
definition en_callfun :: "fname \<Rightarrow> exp list \<Rightarrow> enabled" where
  "en_callfun f values _ \<equiv> do {
    (params, locals, _) \<leftarrow> proc_table f;
    if (list_size params) = (list_size values) then Some True else None
  }"


fun push_stack :: "stack_frame \<Rightarrow> transformer" where
  "push_stack sf (\<sigma>,\<gamma>,\<mu>) = Some (sf#\<sigma>,\<gamma>,\<mu>)"

fun pop_stack :: "transformer" where
  "pop_stack (sf#\<sigma>,\<gamma>,\<mu>) = Some (\<sigma>,\<gamma>,\<mu>)"
| "pop_stack _ = None"

fun top_stack :: "state \<Rightarrow> stack_frame option" where
  "top_stack (sf#\<sigma>,_,_) = Some sf"
| "top_stack _ = None"


definition call_function :: "return_loc \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer"
where "call_function rloc f params_exp s \<equiv> do {
  (formal_params, locals_names, body) \<leftarrow> proc_table f;
  assert (length params_exp = length formal_params);
  (params_val, s) \<leftarrow> real_values params_exp s;
  let locals = 
     map_of (zip formal_params (map Some params_val)) 
  ++ map_of (map (\<lambda>x. (x,None)) locals_names);
  let sf = (body,locals,rloc);
  push_stack sf s
}"

(* The lhs is evaluated before *)
definition tr_callfunl :: "lexp \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer" where
  "tr_callfunl x f call_params s \<equiv> do {
    (addr, s) \<leftarrow> eval_l x s;
    call_function (Ar addr) f call_params s
  }"

definition tr_callfun :: "vname \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer" where
  "tr_callfun x f call_params s \<equiv> do {
    call_function (Vr x) f call_params s
  }"

(* Return eliminates the returning function's stack_frame, then assigns the result to the variable 
   or address where it's supposed to be assigned *)
definition tr_return :: "exp \<Rightarrow> transformer" where
  "tr_return a s = do {
    (v,s) \<leftarrow> eval a s;
    (_,_,ret) \<leftarrow> top_stack s;
    s \<leftarrow> pop_stack s;
    case ret of
      Vr x \<Rightarrow> write_var x v s
    | Ar addr \<Rightarrow> store addr v s
  }"
    
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

| Callfun: "cfg (Callfun x f params) (en_always, tr_callfun x f params) SKIP"
| Callfunl: "cfg (Callfunl x f params) (en_always, tr_callfunl x f params) SKIP"

definition is_empty_stack :: "state \<Rightarrow> bool" where
  "is_empty_stack \<equiv> \<lambda>(\<sigma>,_,_). \<sigma>=[]"

definition com_of :: "state \<Rightarrow> com" where
  "com_of \<equiv> \<lambda>((com,_,_)#_,_,_) \<Rightarrow> com"

definition upd_com :: "com \<Rightarrow> state \<Rightarrow> state" where
  "upd_com \<equiv> \<lambda>com. \<lambda>((_,l,rl)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> ((com,l,rl)#\<sigma>,\<gamma>,\<mu>)"

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
          by (auto split: option_bind_splits)
        thus ?thesis by (fastforce intro: cfg.intros)
      qed
  qed
qed (auto intro: cfg.intros)

lemma cfg_preserves_def_returns:
  assumes "cfg c a c'"
  assumes "def_returns c"
  shows "def_returns c' \<or> (\<exists>e. a=(en_always,tr_return e))"
  using assms
  apply induction
  apply auto
  done

definition coms_of :: "state \<Rightarrow> com set" where
  "coms_of \<equiv> \<lambda>(\<sigma>,_,_). (\<lambda>(com,_,_). com)`set \<sigma>"

lemma coms_of_tuple: "coms_of (\<sigma>,\<gamma>,\<mu>) = (\<lambda>(com,_,_). com)`set \<sigma>"
  unfolding coms_of_def by auto

definition "def_returns_com_stack s \<equiv> \<forall>com\<in>coms_of s. def_returns com"

lemma assert_simps[simp]:
  "assert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"
  "assert \<Phi> = Some () \<longleftrightarrow> \<Phi>"
  unfolding assert_def by auto

lemma "\<not>is_empty_stack s 
  \<Longrightarrow> lift_transformer tr s = Some (r,s') \<Longrightarrow> coms_of s = coms_of s'"
  unfolding lift_transformer_def
  apply (auto 
    simp: is_empty_stack_def
    split: option_bind_splits prod.splits list.splits)
  apply (simp_all add: coms_of_tuple)
  done  

lemma
  assumes "cfg ss (en,tr) ss'"
  assumes "\<not>is_empty_stack s"
  assumes "def_returns_com_stack s"
  assumes "tr s = Some s'"
  shows "def_returns_com_stack s'"
  using assms
  apply cases
  apply (auto simp: def_returns_com_stack_def)

lemma 
  assumes "s \<rightarrow> Some s'"
  assumes "def_returns_com_stack s"
  shows "def_returns_com_stack s'"
  using assms
  apply cases
  

lemma aux:
  assumes "\<not>is_empty_stack s"
  shows "\<exists>x. s \<rightarrow> x"
  using assms
proof -
  from assms obtain c locals rloc \<sigma> \<gamma> \<mu> where "s = ((c,locals,rloc)#\<sigma>, \<gamma>,\<mu>)"
    unfolding is_empty_stack_def
    apply (simp add: neq_Nil_conv split: prod.splits)
    by auto

  from cfg_has_enabled_action[of c] obtain c' en tr 
    where "cfg c (en, tr) c' \<and> (en s = None \<or> en s = Some True)" 


proof (induction c)
  case SKIP thus ?case by simp
next
  case (Assignl x a) [simp] 
  show ?case
  proof (cases "tr_assignl x a s")
    case None[simp]
      hence "(x ::== a, s) \<rightarrow> None" using small_step.None cfg.Assignl by blast
      thus ?thesis by auto
  next
    case (Some s\<^sub>2)[simp]
      hence "(x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using small_step.Base cfg.Assignl by blast
      thus ?thesis by auto
  qed
next
  case (Assign x a)
  show ?case 
  proof (cases "tr_assign x a s")
    case None[simp]
      hence "(x ::= a, s) \<rightarrow> None" using small_step.None cfg.Assign by blast
      thus ?thesis using Assign by auto
    next
    case (Some s\<^sub>2)[simp]
      hence "(x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using small_step.Base cfg.Assign by blast
      thus ?thesis using Assign by auto
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "c\<^sub>1 = SKIP")
    case True
    hence "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)" using cfg.Seq1 small_step.Base by blast
    thus ?thesis using Seq `c\<^sub>1 = SKIP` by auto
  next
    case False
    from Seq.IH(1)[OF this] obtain a where "(c\<^sub>1,s) \<rightarrow> a" ..
    thus ?thesis
    proof cases
      case (Base en tr c\<^sub>1' s\<^sub>2)
      from Seq2[OF Base(2), of c\<^sub>2] Base show ?thesis
        by (auto intro: small_step.Base)
    next    
      case (None en tr c\<^sub>1')
      from Seq2[OF None(2), of c\<^sub>2] None show ?thesis
        by (auto intro: small_step.None)
    qed
  qed
next
  case (If b c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "en_pos b s")
    case None[simp]
      hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None" using cfg.IfTrue small_step.None by blast
      thus ?thesis using If by auto
  next
    case (Some a)[simp]
      show ?thesis
      proof (cases "tr_eval b s")
        case None
          hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None" using cfg.IfTrue small_step.None by blast
          thus ?thesis using If by auto
      next
        case (Some s\<^sub>2)
          show ?thesis
          proof (cases a)
            case True
              hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>1, s\<^sub>2)"
              using `en_pos b s = Some a` cfg.IfTrue small_step.Base If Some by metis
              thus ?thesis using If by auto
          next
            case False[simp]
            have "en_pos b s = Some False" by simp
            hence "en_neg b s = Some True"
              unfolding en_pos_def en_neg_def
              by (auto split: option_bind_splits)
            hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
            using `tr_eval b s = Some s\<^sub>2` cfg.IfFalse small_step.Base If Some by metis
            thus ?thesis using If by auto
          qed
      qed
  qed
next
case (While b c)
  thus ?case using small_step.Base cfg.While by blast
next
case (Free x)
  show ?case
  proof (cases "tr_free x s")
    case None
      hence "(FREE x, s) \<rightarrow> None" using cfg.Free small_step.None by blast
      thus ?thesis using Free by auto
  next
    case (Some s\<^sub>2)
      hence "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using cfg.Free small_step.Base by blast
      thus ?thesis using Free by auto
  qed
next
  case (Return a)
    thus ?case
    proof (cases "tr_return a s")
      case None
        hence "(Return a, s) \<rightarrow> None" using cfg.Return small_step.None by blast
        thus ?thesis by auto
    next
      case (Some s\<^sub>2)
        hence "(Return a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using cfg.Return small_step.Base by blast
        thus ?thesis by auto
    qed
next
  case (Callfun x f params)
    thus ?case
    proof (cases "tr_callfun x f params s")
      case None
        hence "(Callfun x f params, s) \<rightarrow> None" using cfg.Callfun small_step.None by blast
        thus ?thesis by auto
    next
      case (Some s\<^sub>2)
        hence "(Callfun x f params, s) \<rightarrow> Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)" 
          using cfg.Callfun small_step.Base by blast
        thus ?thesis by auto
    qed
next
  case (Callfunl x f params)
    thus ?case
    proof (cases "tr_callfunl x f params s")
      case None
        hence "(Callfunl x f params, s) \<rightarrow> None" using cfg.Callfunl small_step.None by blast
        thus ?thesis by auto
    next
      case (Some s\<^sub>2)
        hence "(Callfunl x f params, s) \<rightarrow> Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)" 
          using cfg.Callfunl small_step.Base by blast
        thus ?thesis by auto
    qed
next
  case (Block c)
    thus ?case sorry
qed


lemma cfg_SKIP_stuck[simp]: "\<not> cfg SKIP a c"
  by (auto elim: cfg.cases)

lemma ss_SKIP_stuck[simp]: "\<not>( (SKIP,s) \<rightarrow> cs')"
  by (auto elim: small_step.cases)

lemma ss'_SKIP_stuck[simp]: "\<not>( Some (SKIP,s) \<rightarrow>' cs')"
  by (auto elim: small_step'.cases)


lemma en_neg_by_pos: "en_neg e s = map_option (HOL.Not) (en_pos e s)"
  unfolding en_pos_def en_neg_def
  by (auto split: option_bind_splits)

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
  prefer 3
  apply (erule cfg.cases, auto) []
  prefer 3
  apply (erule cfg.cases, auto) []
  sorry

lemma small_step_determ:
  assumes "(c,s) \<rightarrow> c'"
  assumes "(c,s) \<rightarrow> c''"
  shows "c'=c''"
  using assms
  apply (cases)
  apply (erule small_step.cases)
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos) []
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos) []
  apply (erule small_step.cases)
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos) []
  by simp

(* Return is undefined because we will never have a Return command outside of a Block or Blockl
   Callfunl is giving me problems *)
fun fstep :: "com \<times> state \<Rightarrow> (com \<times> state) option" where
  "fstep (SKIP,s) = Some (SKIP,s)"
| "fstep (x ::= a,s) = do {
    s \<leftarrow> tr_assign x a s;
    Some (SKIP,s)
  }"
| "fstep (x ::== a,s) = do {
    s \<leftarrow> tr_assignl x a s;
    Some (SKIP,s)
  }"
| "fstep (SKIP;;c, s) = Some (c,s)"
| "fstep (c\<^sub>1;; c\<^sub>2, s) = do {
    (c\<^sub>1', s) \<leftarrow> fstep (c\<^sub>1, s);
    Some (c\<^sub>1' ;; c\<^sub>2, s)
  }"
| "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = do {
    v \<leftarrow> en_pos b s;
    s \<leftarrow> tr_eval b s;
    if v then Some (c\<^sub>1, s) else Some (c\<^sub>2, s)
  }"
| "fstep (WHILE b DO c, s) = Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
| "fstep (FREE x, s) = do {
    s \<leftarrow> tr_free x s;
    Some (SKIP, s)
  }"
| "fstep (Return a, s) = do {
    s \<leftarrow> tr_return a s;
     Some (SKIP, s)
  }"
| "fstep (Block c, s) = do {
    (c, s) \<leftarrow> fstep (c, s);
    Some (Block c, s)
  }"
| "fstep (Callfun x f params, s) = do {
    s \<leftarrow> tr_callfun x f params s;
    Some (Block (snd (snd (the (proc_table f)))), s)
  }"
| "fstep (Callfunl x f params, s) = do {
    s \<leftarrow> tr_callfunl x f params s;
    Some (Block (snd (snd (the (proc_table f)))), s)
  }"


lemma fstep_seq_nSKIP[simp]: "c\<^sub>1 \<noteq> SKIP \<Longrightarrow> fstep (c\<^sub>1;; c\<^sub>2, s) = do {
    (c\<^sub>1', s) \<leftarrow> fstep (c\<^sub>1, s);
    Some (c\<^sub>1' ;; c\<^sub>2, s)
  }"
  by (cases c\<^sub>1) auto


lemma fstep1: "(c,s) \<rightarrow> c' \<Longrightarrow> fstep (c,s) = c'"
proof (induction c arbitrary: s c')
  case SKIP
    hence False using cfg.cases small_step.cases by fastforce
    thus ?case by auto
next
  case (Assignl x a)
    thus ?case
    proof (cases "tr_assignl x a s")
    print_cases
      case None
        hence "fstep (x ::== a, s) = None" by auto
        moreover have "(x ::== a, s) \<rightarrow> None" using None cfg.Assignl small_step.None by blast
        ultimately show ?thesis using Assignl small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (x ::== a, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assignl small_step.Base by blast
        ultimately show ?thesis using Assignl small_step_determ by simp
    qed
next
  case (Assign x a)
  thus ?case
  proof (cases "tr_assign x a s")
  print_cases
    case None
      hence "fstep (x ::= a, s) = None" by auto
      moreover have "(x ::= a, s) \<rightarrow> None" using None cfg.Assign small_step.None by blast
      ultimately show ?thesis using Assign small_step_determ by simp
  next
    case (Some s\<^sub>2)
      hence "fstep (x ::= a, s) = Some (SKIP, s\<^sub>2)" by auto
      moreover have "(x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assign small_step.Base by blast
      ultimately show ?thesis using Assign small_step_determ by simp
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  from Seq.prems show ?case
  proof cases
    case (Base en tr c\<^sub>1' s\<^sub>2)
    note [simp] = Base(1)
    from Base(2) show ?thesis
    proof cases
      case Seq1
      thus ?thesis
        using Base
        by simp
    next
      case (Seq2 cc\<^sub>1)
      hence [simp]: "c\<^sub>1 \<noteq> SKIP" by auto

      from Base(3,4) Seq2(2) have "(c\<^sub>1,s) \<rightarrow> Some (cc\<^sub>1,s\<^sub>2)"
        by (blast intro: small_step.intros)
      from Seq.IH(1)[OF this] have [simp]: "fstep (c\<^sub>1, s) = Some (cc\<^sub>1, s\<^sub>2)" by simp

      show ?thesis using \<open>c\<^sub>1' = cc\<^sub>1;; c\<^sub>2\<close>
        by simp
    qed
  next
    case (None en tr c\<^sub>1')
    note [simp] = \<open>c'=None\<close>
    from None(2) show ?thesis
    proof cases
      case Seq1 with None(3) have False by auto thus ?thesis ..
    next
      case (Seq2 cc1)
      hence [simp]: "c\<^sub>1 \<noteq> SKIP" by auto

      from None(3) Seq2(2) have "(c\<^sub>1,s) \<rightarrow> None"
        by (blast intro: small_step.intros)
      from Seq.IH(1)[OF this] have [simp]: "fstep (c\<^sub>1, s) = None" .
      show ?thesis
        by simp
    qed
  qed
next
  case (If b c\<^sub>1 c\<^sub>2)
  thus ?case
  proof (cases "en_pos b s")
    case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis using If small_step_determ by simp
  next
    case (Some v)
    thus ?thesis
    proof (cases "tr_eval b s")
      case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis using If small_step_determ by simp
    next
      case (Some s\<^sub>2)
      thus ?thesis
      proof (cases v)
        case True
          hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>1, s\<^sub>2)" using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>1, s\<^sub>2)"
            using Some cfg.IfTrue small_step.Base `en_pos b s = Some v` `v` by metis
          ultimately show ?thesis using If small_step_determ by simp
      next
        case False[simp]
          have "en_pos b s = Some False" using `en_pos b s = Some v` by simp
          hence "en_neg b s = Some True" using en_neg_by_pos by auto
          moreover have "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>2, s\<^sub>2)"
            using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
            using Some cfg.IfFalse small_step.Base calculation(1) by metis
          ultimately show ?thesis using If small_step_determ by simp
      qed
    qed
  qed
next
  case (While b c)
    hence "fstep (WHILE b DO c, s) = Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)" by auto
    moreover have "(WHILE b DO c, s) \<rightarrow> Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
      using cfg.While small_step.Base by blast
    ultimately show ?case using While small_step_determ by simp
next
  case (Free x)
    thus ?case
    proof (cases "tr_free x s")
      case None
        hence "fstep (FREE x, s) = None" by auto
        moreover have "(FREE x, s) \<rightarrow> None" using None cfg.Free small_step.None by blast
        ultimately show ?thesis using Free small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (FREE x, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Free small_step.Base by blast
        ultimately show ?thesis using Free small_step_determ by simp
    qed
print_cases
next
  case (Return a)
    thus ?case
    proof (cases "tr_return a s")
      case None
        hence "fstep (Return a, s) = None" by auto
        moreover have "(Return a, s) \<rightarrow> None" using None cfg.Return small_step.None by blast
        ultimately show ?thesis using Return small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (Return a, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(Return a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Return small_step.Base by blast
        ultimately show ?thesis using Return small_step_determ by simp
    qed
next
  case (Callfun x f params)
    thus ?case
    proof (cases "tr_callfun x f params s")
      case None
        hence "fstep (Callfun x f params, s) = None" by simp
        moreover have "(Callfun x f params, s) \<rightarrow> None"
          using cfg.Callfun small_step.None None by blast
        ultimately show ?thesis using Callfun small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (Callfun x f params, s) = Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)"
          by simp
        moreover have "(Callfun x f params, s) \<rightarrow> Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)" 
          using cfg.Callfun small_step.Base Some by blast
        ultimately show ?thesis using Callfun small_step_determ by simp
    qed
next
  case (Callfunl x f params)
    thus ?case
    proof (cases "tr_callfunl x f params s")
      case None
        hence "fstep (Callfunl x f params, s) = None" by simp
        moreover have "(Callfunl x f params, s) \<rightarrow> None"
          using cfg.Callfunl small_step.None None by blast
        ultimately show ?thesis using Callfunl small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (Callfunl x f params, s) = Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)"
          by simp
        moreover have "(Callfunl x f params, s) \<rightarrow> Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)" 
          using cfg.Callfunl small_step.Base Some by blast
        ultimately show ?thesis using Callfunl small_step_determ by simp
    qed
next
  case (Block c)
    thus ?case sorry
qed


lemma fstep2: "c\<noteq>SKIP \<Longrightarrow> (c,s) \<rightarrow> (fstep (c,s))"
proof (induction c)
  case SKIP
    thus ?case by simp
next
  case (Assignl x a)
  thus ?case
  proof (cases "tr_assignl x a s")
  print_cases
    case None
      hence "fstep (x ::== a, s) = None" by auto
      moreover have "(x ::== a, s) \<rightarrow> None" using None cfg.Assignl small_step.None by blast
      ultimately show ?thesis by auto
  next
    case (Some s\<^sub>2)
      hence "fstep (x ::== a, s) = Some (SKIP, s\<^sub>2)" by auto
      moreover have "(x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assignl small_step.Base by blast
      ultimately show ?thesis by auto
  qed
next
  case (Assign x a)
  thus ?case
  proof (cases "tr_assign x a s")
  print_cases
    case None
      hence "fstep (x ::= a, s) = None" by auto
      moreover have "(x ::= a, s) \<rightarrow> None" using None cfg.Assign small_step.None by blast
      ultimately show ?thesis by auto
  next
    case (Some s\<^sub>2)
      hence "fstep (x ::= a, s) = Some (SKIP, s\<^sub>2)" by auto
      moreover have "(x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assign small_step.Base by blast
      ultimately show ?thesis by auto
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case
  proof (cases "c\<^sub>1 = SKIP")
    case True
      hence "fstep (SKIP;; c\<^sub>2, s) = Some (c\<^sub>2, s)" using small_step.Base cfg.Seq1 fstep1 by blast
      moreover have "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)" using cfg.Seq1 small_step.Base by blast
      ultimately show ?thesis using Seq `c\<^sub>1 = SKIP` by auto
  next
    case False
      from Seq.IH(1)[OF this] obtain a where "(c\<^sub>1, s) \<rightarrow> a" ..
      thus ?thesis
      proof cases
        case (Base en tr c\<^sub>1' s\<^sub>2)
          from Seq2[OF Base(2), of c\<^sub>2] Base
            have "(c\<^sub>1 ;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>1' ;; c\<^sub>2, s\<^sub>2)" using small_step.Base by auto
          moreover have "fstep (c\<^sub>1 ;; c\<^sub>2, s) = Some (c\<^sub>1' ;; c\<^sub>2, s\<^sub>2)" using fstep1 calculation by blast
          ultimately show ?thesis by auto
      next
        case (None en tr c\<^sub>1')
          from Seq2[OF None(2), of c\<^sub>2] None
            have "(c\<^sub>1 ;; c\<^sub>2, s) \<rightarrow>None" using small_step.None by auto
          moreover have "fstep (c\<^sub>1 ;; c\<^sub>2, s) = None" using fstep1 calculation by blast
          ultimately show ?thesis by auto
      qed
  qed
next
  case (If b c\<^sub>1 c\<^sub>2)
  thus ?case
  proof (cases "en_pos b s")
    case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis by auto
  next
    case (Some v)
    thus ?thesis
    proof (cases "tr_eval b s")
      case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis by auto
    next
      case (Some s\<^sub>2)
      thus ?thesis
      proof (cases v)
        case True
          hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>1, s\<^sub>2)" using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>1, s\<^sub>2)"
            using Some cfg.IfTrue small_step.Base `en_pos b s = Some v` `v` by metis
          ultimately show ?thesis by auto
      next
        case False[simp]
          have "en_pos b s = Some False" using `en_pos b s = Some v` by simp
          hence "en_neg b s = Some True" using en_neg_by_pos by auto
          moreover have "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>2, s\<^sub>2)"
            using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
            using Some cfg.IfFalse small_step.Base calculation(1) by metis
          ultimately show ?thesis by auto
      qed
    qed
  qed
next
  case (While b c)
    hence "fstep (WHILE b DO c, s) = Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)" by auto
    moreover have "(WHILE b DO c, s) \<rightarrow> Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
      using cfg.While small_step.Base by blast
    ultimately show ?case by auto
next
  case (Free x)
    thus ?case
    proof (cases "tr_free x s")
      case None
        hence "fstep (FREE x, s) = None" by auto
        moreover have "(FREE x, s) \<rightarrow> None" using None cfg.Free small_step.None by blast
        ultimately show ?thesis by auto
    next
      case (Some s\<^sub>2)
        hence "fstep (FREE x, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Free small_step.Base by blast
        ultimately show ?thesis by auto
    qed
next
  case (Return a)
    thus ?case
    proof (cases "tr_return a s")
      case None
        hence "fstep (Return a, s) = None" by auto
        moreover have "(Return a, s) \<rightarrow> None" using None cfg.Return small_step.None by blast
        ultimately show ?thesis using Return small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (Return a, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(Return a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Return small_step.Base by blast
        ultimately show ?thesis using Return small_step_determ by simp
    qed
next
  case (Callfun x f params)
    thus ?case
    proof (cases "tr_callfun x f params s")
      case None
        hence "fstep (Callfun x f params, s) = None" by simp
        moreover have "(Callfun x f params, s) \<rightarrow> None"
          using cfg.Callfun small_step.None None by blast
        ultimately show ?thesis using Callfun small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (Callfun x f params, s) = Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)"
          by simp
        moreover have "(Callfun x f params, s) \<rightarrow> Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)" 
          using cfg.Callfun small_step.Base Some by blast
        ultimately show ?thesis using Callfun small_step_determ by simp
    qed
next
  case (Callfunl x f params)
    thus ?case
    proof (cases "tr_callfunl x f params s")
      case None
        hence "fstep (Callfunl x f params, s) = None" by simp
        moreover have "(Callfunl x f params, s) \<rightarrow> None"
          using cfg.Callfunl small_step.None None by blast
        ultimately show ?thesis using Callfunl small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (Callfunl x f params, s) = Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)"
          by simp
        moreover have "(Callfunl x f params, s) \<rightarrow> Some (Block (snd (snd (the (proc_table f)))), s\<^sub>2)" 
          using cfg.Callfunl small_step.Base Some by blast
        ultimately show ?thesis using Callfunl small_step_determ by simp
    qed
next
  case (Block c)
    thus ?case sorry
qed


fun is_term :: "(com\<times>state) option \<Rightarrow> bool" where
  "is_term (Some (SKIP,_)) = True"
| "is_term None = True"
| "is_term _ = False"


definition interp :: "com \<times> state \<Rightarrow> (com\<times>state) option" where
  "interp cs \<equiv> (while
    (HOL.Not o is_term)
    (\<lambda>Some cs \<Rightarrow> fstep cs)
    (Some cs))"

lemma interp_unfold: "interp cs = (
    if is_term (Some cs) then
      Some cs
    else do {
      cs \<leftarrow> fstep cs;
      interp cs
    }
  )"
  unfolding interp_def
  apply (subst while_unfold)
  apply (auto split: option_bind_split)
  apply (subst while_unfold)
  apply auto
  done


lemma interp_term: "is_term (Some cs) \<Longrightarrow> interp cs = Some cs"
  apply (subst interp_unfold)
  by simp

definition "yields == \<lambda>cs cs'. Some cs \<rightarrow>* cs' \<and> is_term cs'"
definition "terminates == \<lambda>cs. \<exists>cs'. yields cs cs'"

lemma None_star_preserved[simp]: "None \<rightarrow>* z \<longleftrightarrow> z=None"
proof
  assume "None \<rightarrow>* z"
  thus "z=None"
    apply (induction "None::(com\<times>state) option" z rule: star.induct)
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
  shows "(yields cs cs') \<longleftrightarrow> (cs' = interp cs)"
proof safe
  assume "yields cs cs'"
  hence a: "Some cs \<rightarrow>* cs'" and b: "is_term cs'" unfolding yields_def by auto
  thus "cs' = interp cs"
  proof (induction _ "Some cs" _ arbitrary: cs rule: star.induct)
    case refl with interp_term show ?case by simp
  next
    case (step csh cs')
    from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "fstep cs = csh"
      apply (cases)
      apply (cases cs, cases csh)
      apply (auto intro: fstep1)
      done

    from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_term (Some cs)"
      apply (cases "Some cs" rule: is_term.cases)
      by simp_all

    show ?case
    proof (cases csh)
      case None[simp]

      from \<open>csh \<rightarrow>* cs'\<close> have [simp]: "cs'=None" by simp

      show ?thesis
        by (subst interp_unfold) simp
    next
      case (Some cst)[simp]

      have "interp cs = interp cst"
        by (subst interp_unfold) simp
      thus ?thesis using step.hyps(3)[OF Some step.prems]
        by simp
    qed
  qed
next
  from TERM obtain cs' where
    1: "Some cs \<rightarrow>* cs'" "is_term cs'"
    unfolding yields_def terminates_def by auto
  hence "cs'=interp cs"
  proof (induction "Some cs" _ arbitrary: cs rule: star.induct)
    case refl thus ?case by (simp add: interp_term)
  next
    case (step csh cs')

    from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "fstep cs = csh"
      apply (cases)
      apply (cases cs, cases csh)
      apply (auto intro: fstep1)
      done

    from \<open>Some cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_term (Some cs)"
      apply (cases "Some cs" rule: is_term.cases)
      by simp_all

    show ?case
    proof (cases csh)
      case None[simp]

      from \<open>csh \<rightarrow>* cs'\<close> have [simp]: "cs'=None" by simp

      show ?thesis
        by (subst interp_unfold) simp
    next
      case (Some cst)[simp]

      have "interp cs = interp cst"
        by (subst interp_unfold) simp
      thus ?thesis using step.hyps(3)[OF Some step.prems]
        by simp
    qed
  qed
  with 1 have "Some cs \<rightarrow>* interp cs" "is_term (interp cs)" by simp_all
  thus "yields cs (interp cs)" by (auto simp: yields_def)
qed


lemmas [code] = interp_unfold

export_code interp in SML


end

