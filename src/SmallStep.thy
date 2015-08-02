theory SmallStep
imports
  "~~/src/HOL/IMP/Star"
  "~~/src/HOL/Library/While_Combinator"
  Eval
begin

section \<open>Small Step Semantics\<close>

subsection \<open>CFG\<close>

text \<open>A CFG (Control Flow Graph) is a grahp representation of all paths that can be taken by a
  program during its execution.

  Here we define a CFG for our semantics with all the possible steps that it can take from one
  command to another.

  The nodes are defined as commands and the edges are labeled by an enabled and a transformer
  function. The enabled function indicates if the state is enabled to traverse this edge of the
  CFG from command1 to command2, and the transformer indicates the state that would result from
  taking this edge in the CFG.\<close>

subsection \<open>Type definitions\<close>

text \<open>An @{term enabled} is a partial function from @{term state} to @{term bool} that indicates whether
  an execution is enabled to continue.\<close>
type_synonym enabled = "state \<rightharpoonup> bool"

text \<open>A @{term transformer} is a partial function from @{term state} to @{term state} that
  applies a transformation to the first @{term state} and returns the second.\<close>
type_synonym transformer = "state \<rightharpoonup> state"

text \<open>A CFG lable consists of a pair containing an @{term enabled} and a @{term state}.\<close>
type_synonym cfg_label = "enabled \<times> transformer"

locale program =
  fixes program :: program
  assumes valid: "valid_program proc_table"
begin
  definition "proc_table == proc_table_of program"
end

subsection \<open>Definition of initial state\<close>

text \<open>We proceed to define the components necessary to build the initial state. For it we need:
  * Initial stack: The initial stack is a stack that only contains the stack frame for the
      main function.
  * Initial globals: The initial globals is a valuation that returns None as the value for each
      of the globals of the program.
  * Initial memory: The initial memory is an empty list.

  Finally the initial state is the join of the initial stack, the initial globals and the
  initial memory.
\<close>
context fixes program :: program begin

  private definition "proc_table \<equiv> proc_table_of program"

  definition "main_decl \<equiv> the (proc_table ''main'')"
  definition "main_local_names \<equiv> fun_decl.locals main_decl"
  definition "main_com \<equiv> fun_decl.body main_decl"

  definition initial_stack :: "stack_frame list" where
    "initial_stack \<equiv> [(main_com,map_of (map (\<lambda>x. (x,None)) main_local_names),Invalid)]"
  definition initial_glob :: valuation where 
    "initial_glob \<equiv> map_of (map (\<lambda>x. (x,None)) (program.globals program))"
  definition initial_mem :: mem where "initial_mem \<equiv> []"
  definition initial_state :: state 
    where "initial_state \<equiv> (initial_stack, initial_glob, initial_mem)"

end

text \<open>id functions for enabled and transformer\<close>
abbreviation en_always :: enabled where "en_always \<equiv> \<lambda>_. Some True"
abbreviation (input) tr_id :: transformer where "tr_id \<equiv> Some"

subsection \<open>Enabled functions\<close>

text \<open>In this semantics the only reason why a node wouldn't be enabled to continue is if a
  condition would evaluate to True and we were trying to take the edge for the False branch
  or viceversa.\<close>

text \<open>We have no bool values in our semantics. Instead we have to interpret our values as
  True or False. Any value different from @{term NullVal} or @{term "I 0"} is True, on the other
  hand @{term NullVal} and @{term "I 0"} would both be False.\<close>
fun truth_value_of :: "val \<Rightarrow> bool" where
  "truth_value_of NullVal \<longleftrightarrow> False"
| "truth_value_of (I i) \<longleftrightarrow> i\<noteq>0"
| "truth_value_of (A _) \<longleftrightarrow> True"

text \<open>Given an expression, typically the condition for an if branch, we will evaluate the
  true value of that expression and then return that boolean value.
  We want to know if we're enabled to continue to the true branch of the conditional.\<close>
definition en_pos :: "exp \<Rightarrow> enabled" where
  "en_pos e s \<equiv> do {
    (v,_) \<leftarrow> lift_transformer (eval e) s;
    let b = truth_value_of v;
    Some b
  }"

text \<open>Given an expression, typically the condition for an if branch, we will evaluate the
  true value of that expression and then return that boolean value.
  We want to know if we're enabled to continue to the false branch of the conditional, therefore
  we return the negation of the boolean value.\<close>
definition en_neg :: "exp \<Rightarrow> enabled" where
  "en_neg e s \<equiv> do {
    (v,_) \<leftarrow> lift_transformer (eval e) s;
    let b = truth_value_of v;
    Some (\<not>b)
  }"

subsection \<open>Transformer functions\<close>

text \<open>A transformer function has return type @{term "state option"} It returns
  None if there's an error at some point in the execution. Otherwise it'll return Some state.\<close>

text \<open>The transformer for an assignment will evaluate the expression we want to assign
  and then proceed to write the value to the state, it returns the state resulting from
  doing this write.\<close>
definition "tr_assign x a \<equiv> lift_transformer_nr (\<lambda>s. do {
  (v,s) \<leftarrow> eval a s;
  s \<leftarrow> write_var x v s;
  Some s
})"

text \<open>The transformer for an assignment to an address will first evaluate the l-expression to
  obtain the address in which we want to store the value, then it will evaluate the expression
  we want to store and then proceed to store the value, it returns the state resulting from
  doing this store.\<close>
definition tr_assignl :: "lexp \<Rightarrow> exp \<Rightarrow> transformer"
where "tr_assignl x a \<equiv> lift_transformer_nr (\<lambda>s. do {
  (addr,s) \<leftarrow> eval_l x s;
  (v,s) \<leftarrow> eval a s;
  store addr v s
})"

text \<open>The transformer for an evaluation will evaluate the expression and proceed to return the
  state resulting from evaluating this expression.\<close>
definition tr_eval :: "exp \<Rightarrow> transformer" where
  "tr_eval e \<equiv> lift_transformer_nr (\<lambda>s. do {
    (_,s) \<leftarrow> eval e s;
    Some s
  })"

text \<open>The transformer for a free operation will evaluate the l-expression it receives to obtain
  the address it will free in memory and proceeds to execute the free operation.\<close>
definition tr_free :: "lexp \<Rightarrow> transformer" where
  "tr_free e \<equiv> lift_transformer_nr (\<lambda>s. do {
    (addr, s) \<leftarrow> eval_l e s;
    s \<leftarrow> free addr s;
    Some s
  })"

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

text \<open>We write some auxiliary functions for push, popping and returning the top of the stack.\<close>

fun push_stack :: "stack_frame \<Rightarrow> transformer" where
  "push_stack sf (\<sigma>,\<gamma>,\<mu>) = Some (sf#\<sigma>,\<gamma>,\<mu>)"

fun pop_stack :: "transformer" where
  "pop_stack (sf#\<sigma>,\<gamma>,\<mu>) = Some (\<sigma>,\<gamma>,\<mu>)"
| "pop_stack _ = None"

fun top_stack :: "state \<Rightarrow> stack_frame option" where
  "top_stack (sf#\<sigma>,_,_) = Some sf"
| "top_stack _ = None"


text \<open>When calling a function we make the call with the values instead of the expressions.
  @{term real_values} takes an expression list and transforms it into a value list by evaluating
  each expression.\<close>
fun real_values :: "exp list \<Rightarrow> visible_state \<Rightarrow> (val list \<times> visible_state) option" where
  "real_values [] s = Some ([], s)"
| "real_values (x#xs) s = do {
    (v,s) \<leftarrow> eval x s;
    (vals, s) \<leftarrow> real_values xs s;
    Some ([v] @ vals, s)
  }"

text \<open>The difference between calling a function and a procedure is that a function returns
  a value whereas the procedure doesn't. A stack frame has a return location that indicates where
  the caller expects the result of a function call.

  When calling a function, independent from whether it returns or not we must make sure that
  the length of the parameters which we are using to call the function are the same length as
  the formal parameters, then we proceed to evaluate the parameters, this will be done from left
  to right, we set the parameters of the function with their values for the valuation and the
  rest of the locals we set to uninitialized (None).

  With the locals, the functions body and return location invalid we create a new stack frame,
  push it to the stack and return the state.\<close>
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

text \<open>@{term set_rloc} and @{term get_rloc} will allow us to modify the return location of the
  current stack frame.\<close>
definition set_rloc :: "return_loc \<Rightarrow> transformer" where
  "set_rloc rloc \<equiv> \<lambda>((com,locals,_)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> 
    Some ((com,locals,rloc)#\<sigma>,\<gamma>,\<mu>)
  "

definition get_rloc :: "state \<Rightarrow> return_loc" where
  "get_rloc \<equiv> \<lambda>((com,locals,rloc)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> rloc"


text \<open>When a function returns to a l-expression, first of all we evaluate the l-expression
  to obtain the return address. This is the first evaluation we do because if we do it afterwards
  we might risk unwanted behaviour as the function might have changed the state.
  After that we update the return location indicating we expect the function to return to this
  address and we call @{term call_function}.\<close>
definition tr_callfunl :: "proc_table \<Rightarrow> lexp \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer" where
  "tr_callfunl proc_table x f args s \<equiv> do {
    (addr,s) \<leftarrow> lift_transformer (eval_l x) s;
    s \<leftarrow> set_rloc (Ar addr) s;
    call_function proc_table f args s
  }"

text \<open>When a function returns to a variable, we set the return location to that variable
  indicating we expect the function to return to this variable and we call
  @{term call_function}.\<close>
definition tr_callfun :: "proc_table \<Rightarrow> vname \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer" where
  "tr_callfun proc_table x f args s \<equiv> do {
    s \<leftarrow> set_rloc (Vr x) s;
    call_function proc_table f args s
  }"

text \<open>When a function returns to a variable, we set the return location to invalid
  indicating we expect the function to return void and we call @{term call_function}.\<close>
definition tr_callfunv :: "proc_table \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer" where
  "tr_callfunv proc_table f args s \<equiv> do {
    s \<leftarrow> set_rloc Invalid s;
    call_function proc_table f args s
  }"


text \<open>The transformer for return will pop the last stack frame in the stack belonging to the
  returning function, evaluate the value returned by the function and if the stack is not empty
  then proceed to get the return location and depending on if it's a an address, a variable or
  invalid it will store, write or return the state as it is respectively.\<close>
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

text \<open>The transformer for return will pop the last stack frame in the stack belonging to the
  returning function and if the stack is not empty then proceed to get the return location and
  if it's a variable or an address this is an error and returns None, if, on the other hand,
  it's Invalid then it will return the state.\<close>    
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


subsection \<open>Definition of the CFG\<close>

text \<open>The CFG offers a relation that shows the edges that can occur in the context of our
  semantics.

  The following are the relationships permitted in the CFG. In other words they're the possible
  small steps that can be taken when executing a program.
  Each of these rules have the form:

  cfg c\<^sub>1 (enabled, transformer) c\<^sub>2

  This means that in our CFG we would have an edge from c\<^sub>1 to c\<^sub>2 labeled with (enabled, transformer).
  The enabled and transformers used in the CFG definitions are the ones described previously.
\<close>
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
| Returnv: "cfg Returnv (en_always, tr_return_void) SKIP"

| Callfunl: "cfg (Callfunl e f params) (en_always, tr_callfunl proc_table e f params) SKIP"
| Callfun: "cfg (Callfun x f params) (en_always, tr_callfun proc_table x f params) SKIP"
| Callfunv: "cfg (Callfunv f params) (en_always, tr_callfunv proc_table f params) SKIP"

subsection \<open>Definition of the Small Step Semantics\<close>

text \<open>Each stack frame of the stack contains a command, these are the instructions that are
  executed. The initial stack has only one stack frame that has the body of main.

  Since the code we need to execute is there our small step semantics goes from state to state
  option.

  A step in the small step semantics can be taken if the stack is not empty, there's a cfg rule
  from c\<^sub>1 to c\<^sub>2,  the command of the state is c\<^sub>1, the enabled is true and applying the transformer
  to the state with the command updated from c\<^sub>1 to c\<^sub>2 yields a Some s\<^sub>2. If all these conditions
  are met then a small step can go from s to s\<^sub>2.

  If either the enabled or the transformer yield None, there was an error during the execution
  and we take a small step from s to None which is a special error state.

  If the command at the top of the stack is SKIP, the stack is not empty and calling
  @{term tr_return_void} on s yields a new state s\<^sub>2, then we can take a small step from s to s\<^sub>2.

  Finally if the command at the top of the stack is SKIP, the stack is not empty but calling
  @{term tr_return_void} returns None, then we take a small step from s to None, which is a
  special error state.
\<close>
inductive 
  small_step :: "state \<Rightarrow> state option \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
  Base: "\<lbrakk> \<not>is_empty_stack s; c\<^sub>1=com_of s; cfg c\<^sub>1 (en, tr) c\<^sub>2; en s = Some True; tr (upd_com c\<^sub>2 s) = Some s\<^sub>2\<rbrakk> \<Longrightarrow> s \<rightarrow> Some s\<^sub>2"
| None: "\<lbrakk> \<not>is_empty_stack s; c\<^sub>1=com_of s; cfg c\<^sub>1 (en, tr) c\<^sub>2; en s = None     \<or> tr (upd_com c\<^sub>2 s) = None\<rbrakk> \<Longrightarrow>    s \<rightarrow> None"
| Return_void: "\<lbrakk> \<not>is_empty_stack s; com_of s = SKIP; tr_return_void s = Some s' \<rbrakk> \<Longrightarrow> s \<rightarrow> Some s'"
| Return_void_None: "\<lbrakk> \<not>is_empty_stack s; com_of s = SKIP; tr_return_void s = None \<rbrakk> \<Longrightarrow> s \<rightarrow> None"


text \<open>We lift our definition of small step to state option in order to be able to take
  more than one step in the semantics.\<close>
inductive
  small_step' :: "(state) option \<Rightarrow> (state) option \<Rightarrow> bool" (infix "\<rightarrow>' " 55)
where
  "cs \<rightarrow> cs' \<Longrightarrow> Some cs \<rightarrow>' cs'"

text \<open>We can define the execution of a program as the reflexive transitive closure of
  @{term small_step'} by using the star operator.\<close>
abbreviation
  small_steps :: "(state) option \<Rightarrow> (state) option \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step' x y"

subsection \<open>Lemmas regarding the semantics\<close>

text \<open>If a command is not SKIP we prove that there will always be an enabled action it can
  take or an error would occur when executing enabled (a None is returned). The proof for this
  lemma has two interesting cases, namely @{term Seq} and @{term If}.

  In the @{term Seq} case we only have to do a case distinction on whether the first command
  of the sequential composition is SKIP or not. When making that case distinction is clear that
  for both cases there's a cfg rule that ensures an enabled action.

  The @{term If} case is a bit more complicated. We need to make a case distinction over the
  value of @{term "en_pos b s"}, if it's None then the lemma is true. If the value of
  @{term "en_pos b s"} is true then the lemma is also true. The tricky part about
  this proof is that when @{term "en_pos b s"} is False, this in our CFG means that the
  else branch should be taken, therefore when @{term "en_pos b s"} is False, @{term "en_neg b s"}
  will always evaluate to True. Once we prove this the command has an enabled action 
  (@{term "en_neg b s"} \<equiv> True) and the proof of the lemma is complete.
\<close>
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

lemma assert_simps[simp]:
  "assert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"
  "assert \<Phi> = Some () \<longleftrightarrow> \<Phi>"
  unfolding assert_def by auto

text \<open>The following lemma states that as long as the stack is not empty we can always take a
  small step.\<close>
lemma can_take_step:
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

text \<open>cfg gets stuck at SKIP\<close>
lemma cfg_SKIP_stuck[simp]: "\<not> cfg SKIP a c"
  by (auto elim: cfg.cases)

text \<open>An execution is done when we can't take any more steps, this happens when the stack is empty.\<close>
lemma ss_empty_stack_stuck[simp]: "is_empty_stack s \<Longrightarrow> \<not>( s \<rightarrow> cs')"
  by (auto elim: small_step.cases)

lemma ss'_SKIP_stuck[simp]: "is_empty_stack s \<Longrightarrow> \<not>( Some s \<rightarrow>' cs')"
  by (auto elim: small_step'.cases)

text \<open>the result of @{term "en_neg e s"} will always be the negation of the result of
  @{term "en_pos e s"}.\<close>
lemma en_neg_by_pos: "en_neg e s = map_option (HOL.Not) (en_pos e s)"
  unfolding en_pos_def en_neg_def
  by (auto split: Option.bind_splits)

subsection \<open>Determinism\<close>

text \<open>We prove that cfg is deterministic.\<close>
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
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  done

text \<open>We prove that if the stack is not empty it doesn't matter if we update the command first
  and then apply the transformer or the other way around since the transformer works in the
  visible state level and doesn't temper with the command in the top of the stack.\<close>
lemma lift_upd_com: "\<not>is_empty_stack s \<Longrightarrow>
  lift_transformer_nr tr (upd_com c s) = 
  map_option (upd_com c) (lift_transformer_nr tr s)"
  unfolding lift_transformer_nr_def
  by (auto split: prod.splits list.splits Option.bind_split)

text \<open>We prove that if the stack is not empty it doesn't matter if we update the command first
  and then apply the eval transformer or the other way around since the eval transformer works
  in the visible state level and doesn't temper with the command in the top of the stack.\<close>
lemma tr_eval_upd_com: "\<not>is_empty_stack s \<Longrightarrow> 
  tr_eval e (upd_com c s) = map_option (upd_com c) (tr_eval e s)"
  unfolding tr_eval_def
  by (auto simp: lift_upd_com)

text \<open>We prove that small step is deterministic.\<close>
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

section \<open>Executing the semantics\<close>

subsection \<open>Taking a single step in the semantics\<close>

text \<open>We represent two kinds of edges in the cfg. A Base edge that has a transformer,
  is always enabled and takes us to a new command and a Cond edge that apart from the
  transformer also has an enabled and two commands, the enabled indicates whether the
  execution goes to the first or the second command.\<close>
datatype cfg_edge = Base transformer com | Cond enabled transformer com com

context fixes proc_table :: proc_table begin

text \<open>For every command in the semantics we return what kind of step we take in the cfg.\<close>
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
| "cfg_step Returnv = Base (tr_return_void) SKIP"
| "cfg_step (Callfunl e f params) = Base (tr_callfunl proc_table e f params) SKIP"
| "cfg_step (Callfun x f params) = Base (tr_callfun proc_table x f params) SKIP"
| "cfg_step (Callfunv f params) = Base (tr_callfunv proc_table f params) SKIP"

end

context program begin

text \<open>If we have a command different from SKIP and the cfg_step function returns a Base step
  as the kind of step we can take in the CFG then there will be a definition matching this in
  the cfg definition.\<close>
  lemma step_to_cfg_base: "c \<noteq> SKIP \<Longrightarrow> (cfg_step proc_table c = Base tr c') \<Longrightarrow>
      cfg c (en_always,tr) c'"
    apply (induction c arbitrary: tr c' rule: cfg_step.induct)
    apply (auto intro: cfg.intros elim: cfg.cases split: cfg_edge.splits)
    done

text \<open>Also, if we have a command different from SKIP and the cfg_step function returns a Cond
  step as the kind of step we can take in the CFG then there will be a definition matching
  this in the cfg definition.\<close>
  lemma step_to_cfg_cond: "c \<noteq> SKIP \<Longrightarrow> (cfg_step proc_table c = Cond en tr c1' c2') \<Longrightarrow>
    (cfg c (en,tr) c1' \<or> cfg c (map_option HOL.Not o en, tr) c2' )"
    apply (induction c arbitrary: tr c1' c2' rule: cfg_step.induct)
    apply (auto 
      intro: cfg.intros elim: cfg.cases split: cfg_edge.splits simp: en_neg_by_pos)
    apply (force intro: cfg.intros)
    done

text \<open>If we have a cfg rule and the first command is different from SKIP then we will always
  obtain from cfg_step a Base or a Cond step.\<close>
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

text \<open>This is how we take a single step in an execution.
  If the command we need to execute is a SKIP we call the return void transformer.
  Otherwise we will check which kind of step we should take from the @{term cfg_step} function
  and based on that if it's a Base step we will call the transformer with the updated command
  or if it's a Cond we will evaluate the condition and call the transformer with the correct
  updated command.\<close>
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

subsection \<open>Equality between small semantics and single execution\<close>

context program begin

text \<open>@{term fstep1} shows the first direction of this equality. If we can take a step in the
  small step semantics from a state s to a state s' then, executing fstep on that state s will
  yield the same s'.\<close>
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


text \<open>@{term fstep2} shows the other direction of this equality. Assuming the stack is not
  empty then taking a step in the small step semantics from a state s will lead us to a
  to a state s' that is the result of executing fstep on that state s.\<close>
lemma fstep2: "\<not>is_empty_stack s \<Longrightarrow> s \<rightarrow> (fstep proc_table s)"
  unfolding fstep_def
  apply simp apply safe
  apply (cases "tr_return_void s")
  apply (auto intro: small_step.intros) [2]

  apply (simp split: cfg_edge.splits, safe)
  apply (frule (1) step_to_cfg_base)
  apply (metis (no_types, lifting) can_take_step cfg_edge.simps(5) fstep1 fstep_def)
  apply (frule (1) step_to_cfg_cond)
  apply (auto split: Option.bind_splits intro: small_step.intros)
  apply (metis (mono_tags, lifting) can_take_step bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  apply (metis (mono_tags, lifting) can_take_step bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  apply (metis (mono_tags, lifting) can_take_step bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  apply (metis (mono_tags, lifting) can_take_step bind_lunit cfg_edge.simps(6) fstep1 fstep_def)
  done  
  
end

subsection \<open>Interpreter for the semantics\<close>

text \<open>A state is considered final if the stack in that state is empty or if it's None.\<close>
fun is_term :: "state option \<Rightarrow> bool" where
  "is_term (Some s) = is_empty_stack s"
| "is_term None = True"


text \<open>The interpreter for our semantics works as follows:
  As long as we don't reach a final state then we execute @{term fstep}.\<close>
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

text \<open>If the state is final, it is the result of the interpretation.\<close>
lemma interp_term: "is_term (Some cs) \<Longrightarrow> interp proc_table cs = Some cs"
  apply (subst interp_unfold)
  by simp

subsection \<open>Correctness\<close>


context program begin

text \<open>An execution of a state cs yields cs' if we can take steps from cs to cs' and cs' is
  a final state.\<close>
  definition "yields == \<lambda>cs cs'. Some cs \<rightarrow>* cs' \<and> is_term cs'"
text \<open>An execution of a state cs terminates with cs' if it yields cs'.\<close>
  definition "terminates == \<lambda>cs. \<exists>cs'. yields cs cs'"

text \<open>The star operator preserves a None state. If we reach a None in our execution we will
  get stuck in a None state.\<close>
  lemma None_star_preserved[simp]: "None \<rightarrow>* z \<longleftrightarrow> z=None"
  proof
    assume "None \<rightarrow>* z"
    thus "z=None"
      apply (induction "None::(state) option" z rule: star.induct)
      apply (auto elim: small_step'.cases)
      done
  qed auto

text \<open>We prove that @{term small_step'} is deterministic.\<close>
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

text \<open>We want to prove our interpreter is correct, this is: given that the execution terminates
  the execution yields cs' if and only if cs' is the result of interpreting cs.\<close>
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

subsection \<open>Execution of a program\<close>

text \<open>In order to execute a program we will assert that it's valid following the previously
  defined @{term valid_program} definition, and proceed to interpret the initial state of the
  program p.\<close>
definition execute :: "program \<Rightarrow> state option" where
  "execute p \<equiv> do {
    assert (valid_program p);
    interp (proc_table_of p) (initial_state p)
  }"

export_code execute checking SML


end

