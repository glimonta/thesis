theory SmallStep
imports
  "~~/src/HOL/IMP/Star"
  "~~/src/HOL/Library/While_Combinator"
  Eval Type_Checker
begin

(* TODO: Move *)  
definition init_map :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "init_map D f k \<equiv> if k\<in>D then Some (f k) else None"

lemma init_map_app_iff[simp]: 
  "k\<in>D \<Longrightarrow> init_map D f k = Some (f k)"  
  "k\<notin>D \<Longrightarrow> init_map D f k = None"
  unfolding init_map_def by auto

lemma init_map_dom[simp]: "dom (init_map D f) = D"  
  unfolding init_map_def dom_def by auto

lemma init_map_ran[simp]: "ran (init_map D f) = f`D"  
  unfolding init_map_def ran_def by auto

lemma init_map_set_simps[simp]:
  "init_map (D1 \<union> D2) f = init_map D1 f ++ init_map D2 f"
  "init_map (insert x D) f = (init_map D f) (x \<mapsto> f x)"
  unfolding init_map_def[abs_def] 
  by (auto simp: map_add_def)


abbreviation "is_return m \<equiv> \<exists>x. is_res m x" (* TODO: Move*)
fun cp_err :: "('a,'err) error \<Rightarrow> ('b,'err) error" where 
  "cp_err (EAssert e) = EAssert e"
| "cp_err (ENonterm) = ENonterm"
| "cp_err (return _) = undefined"


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
type_synonym enabled = "state \<hookrightarrow> bool"

text \<open>A @{term transformer} is a partial function from @{term state} to @{term state} that
  applies a transformation to the first @{term state} and returns the second.\<close>
type_synonym transformer = "state \<hookrightarrow> state"

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
context program_loc begin

  definition "main_local_names \<equiv> map snd (fun_decl.locals main_decl)"
  definition "main_com \<equiv> fun_decl.body main_decl"

  definition initial_stack :: "stack_frame list" where
    "initial_stack \<equiv> [(main_com,map_of (map (\<lambda>x. (x,None)) main_local_names),Invalid)]"
  definition initial_glob :: valuation where 
    "initial_glob \<equiv> map_of (map (\<lambda>x. (x,None)) (map snd (program.globals p)))"
  definition initial_mem :: mem where "initial_mem \<equiv> []"
  definition initial_state :: state 
    where "initial_state \<equiv> (initial_stack, initial_glob, initial_mem)"

end

text \<open>id functions for enabled and transformer\<close>
abbreviation en_always :: enabled where "en_always \<equiv> \<lambda>_. return True"
abbreviation (input) tr_id :: transformer where "tr_id \<equiv> return"

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
    return b
  }"

text \<open>Given an expression, typically the condition for an if branch, we will evaluate the
  true value of that expression and then return that boolean value.
  We want to know if we're enabled to continue to the false branch of the conditional, therefore
  we return the negation of the boolean value.\<close>
definition en_neg :: "exp \<Rightarrow> enabled" where
  "en_neg e s \<equiv> do {
    (v,_) \<leftarrow> lift_transformer (eval e) s;
    let b = truth_value_of v;
    return (\<not>b)
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
  return s
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
    return s
  })"

text \<open>The transformer for a free operation will evaluate the expression it receives to obtain
  the address it will free in memory and proceeds to execute the free operation.\<close>
definition tr_free :: "exp \<Rightarrow> transformer" where
  "tr_free e \<equiv> lift_transformer_nr (\<lambda>s. do {
    (v, s) \<leftarrow> eval e s;
    case v of
      A addr \<Rightarrow> free addr s
    | NullVal \<Rightarrow> pointer_error  
    | _ \<Rightarrow> type_error 
  })"

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

definition push_stack :: "stack_frame \<Rightarrow> transformer" where
  "push_stack \<equiv> \<lambda>sf (\<sigma>,\<gamma>,\<mu>). return (sf#\<sigma>,\<gamma>,\<mu>)"

fun pop_stack :: "transformer" where
  "pop_stack (sf#\<sigma>,\<gamma>,\<mu>) = return (\<sigma>,\<gamma>,\<mu>)"
| "pop_stack _ = structural_error"

fun top_stack :: "state \<hookrightarrow> stack_frame" where
  "top_stack (sf#\<sigma>,_,_) = return sf"
| "top_stack _ = structural_error"


(* TODO: Move *)
primrec semap :: "('a \<Rightarrow> 's \<hookrightarrow> 'b\<times>'s) \<Rightarrow> 'a list \<Rightarrow> 's \<hookrightarrow> 'b list\<times>'s" where
  "semap _ [] s = return ([],s)"
| "semap f (x#xs) s = do {
    (y,s) \<leftarrow> f x s;
    (ys,s) \<leftarrow> semap f xs s;
    return (y#ys,s)
  }"

lemma semap_length: "semap f xs s = return (ys,s') \<Longrightarrow> length ys = length xs"
  by (induction xs arbitrary: s s' ys) (auto split: Error_Monad.bind_splits)


text \<open>When calling a function we make the call with the values instead of the expressions.
  @{term real_values} takes an expression list and transforms it into a value list by evaluating
  each expression.\<close>
definition real_values :: "exp list \<Rightarrow> visible_state \<hookrightarrow> (val list \<times> visible_state)" where
  "real_values xs s \<equiv> semap eval xs s"

(*
fun real_values :: "exp list \<Rightarrow> visible_state \<hookrightarrow> (val list \<times> visible_state)" where
  "real_values [] s = return ([], s)"
| "real_values (x#xs) s = do {
    (v,s) \<leftarrow> eval x s;
    (vals, s) \<leftarrow> real_values xs s;
    return ([v] @ vals, s)
  }" *)


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

definition mk_locals :: "fun_decl \<Rightarrow> val list \<hookrightarrow> valuation" where
  "mk_locals fd vals \<equiv> do {
    assert (length (fun_decl_param_names fd) = length vals) (EStatic EType);
    return (map_of (zip (fun_decl_param_names fd) (map Some vals)) 
      ++ init_map (set (fun_decl_local_names fd)) (\<lambda>_. None))
  }"

lemma init_map_set[code_unfold]: "init_map (set l) f = map_of (map (\<lambda>x. (x, f x)) l)"
  by (induction l) auto

export_code mk_locals in SML
definition init_frame :: "fun_decl \<Rightarrow> exp list \<Rightarrow> visible_state \<hookrightarrow> (stack_frame \<times> visible_state)"
  where "init_frame fd pexps vs \<equiv> do {
    (pvals,vs) \<leftarrow> real_values pexps vs;
    locals \<leftarrow> mk_locals fd pvals;
    return ((fun_decl.body fd,locals,return_loc.Invalid),vs)
  }"


definition call_function :: "proc_table \<Rightarrow> fname \<Rightarrow> exp list \<Rightarrow> transformer"
where "call_function proc_table f params_exp s \<equiv> do {
  fdecl \<leftarrow> case proc_table f of 
      Some fdecl \<Rightarrow> return fdecl 
    | None \<Rightarrow> type_error;
  (sf,s) \<leftarrow> lift_transformer (init_frame fdecl params_exp) s;
  push_stack sf s
}"

text \<open>@{term set_rloc} and @{term get_rloc} will allow us to modify the return location of the
  current stack frame.\<close>
definition set_rloc :: "return_loc \<Rightarrow> transformer" where
  "set_rloc rloc \<equiv> \<lambda>((com,locals,_)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> 
    return ((com,locals,rloc)#\<sigma>,\<gamma>,\<mu>)
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
      | Invalid \<Rightarrow> return s
    else
      return s
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
        Ar addr \<Rightarrow> type_error
      | Vr x \<Rightarrow> type_error
      | Invalid \<Rightarrow> return s
    else
      return s
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
context program_loc begin

datatype cfg_edge_type = ET_Intra | ET_Call | ET_Return

text \<open>A CFG label consists of a pair containing an @{term enabled} and a @{term state}.\<close>
type_synonym cfg_label = "cfg_edge_type \<times> enabled \<times> transformer"

inductive cfg :: "com \<Rightarrow> cfg_label \<Rightarrow> com \<Rightarrow> bool" where
  Assign: "cfg (x ::= a) (ET_Intra,en_always,tr_assign x a) SKIP"
| Assignl: "cfg (x ::== a) (ET_Intra,en_always,tr_assignl x a) SKIP"
| Seq1: "cfg (SKIP;; c\<^sub>2) (ET_Intra,en_always, tr_id) c\<^sub>2"
| Seq2: "\<lbrakk>cfg c\<^sub>1 a c\<^sub>1'\<rbrakk> \<Longrightarrow> cfg (c\<^sub>1;; c\<^sub>2) a (c\<^sub>1';; c\<^sub>2)"
| IfTrue: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (ET_Intra,en_pos b, tr_eval b) c\<^sub>1"
| IfFalse: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (ET_Intra,en_neg b, tr_eval b) c\<^sub>2"
| While: "cfg (WHILE b DO c) (ET_Intra,en_always, tr_id) (IF b THEN c;; WHILE b DO c ELSE SKIP)"
| Free: "cfg (FREE x) (ET_Intra,en_always, tr_free x) SKIP"

| Return: "cfg (Return a) (ET_Return,en_always, tr_return a) SKIP"
| Returnv: "cfg Returnv (ET_Return,en_always, tr_return_void) SKIP"

| Callfunl: "cfg (Callfunl e f params) (ET_Call,en_always, tr_callfunl proc_table e f params) SKIP"
| Callfun: "cfg (Callfun x f params) (ET_Call,en_always, tr_callfun proc_table x f params) SKIP"
| Callfunv: "cfg (Callfunv f params) (ET_Call,en_always, tr_callfunv proc_table f params) SKIP"

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
  small_step :: "state \<Rightarrow> state ce \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
  Base: "\<lbrakk> \<not>is_empty_stack s; c\<^sub>1=com_of s; cfg c\<^sub>1 (_, en, tr) c\<^sub>2; en s = return True; s'= tr (upd_com c\<^sub>2 s)\<rbrakk> \<Longrightarrow> s \<rightarrow> s'"
| En_fail: "\<lbrakk> \<not>is_empty_stack s; c\<^sub>1=com_of s; cfg c\<^sub>1 (_, en, tr) c\<^sub>2; \<not>is_return (en s); s'=cp_err (en s)\<rbrakk> \<Longrightarrow> s \<rightarrow> s'"
| Return_void: "\<lbrakk> \<not>is_empty_stack s; com_of s = SKIP; s'= tr_return_void s\<rbrakk> \<Longrightarrow> s \<rightarrow> s'"


text \<open>We lift our definition of small step to state option in order to be able to take
  more than one step in the semantics.\<close>
inductive
  small_step' :: "(state) ce \<Rightarrow> (state) ce \<Rightarrow> bool" (infix "\<rightarrow>' " 55)
where
  "cs \<rightarrow> cs' \<Longrightarrow> return cs \<rightarrow>' cs'"

text \<open>We can define the execution of a program as the reflexive transitive closure of
  @{term small_step'} by using the star operator.\<close>
abbreviation
  small_steps :: "(state) ce \<Rightarrow> (state) ce \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
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
  shows "\<exists>c' et en tr. cfg c (et,en,tr) c' \<and> (\<not>is_return (en s) \<or> en s = return True)" 
  using assms
proof (induction c)
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "c\<^sub>1 = SKIP")
    case True
    thus ?thesis by (force intro: cfg.intros)
  next
    case False
    from Seq.IH(1)[OF this] show ?thesis by (force intro: cfg.intros)
  qed  
next
  case (If b c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "en_pos b s")
    case (EAssert e)[simp]
    thus ?thesis by (fastforce intro: cfg.intros)
  next
    case (ENonterm)[simp]  
    thus ?thesis by (fastforce intro: cfg.intros)
  next
    case (return a)[simp]
      show ?thesis
      proof (cases a)
        case True
        thus ?thesis by (fastforce intro: cfg.intros)
      next
        case False[simp]
        have "en_pos b s = return False" by simp
        hence "en_neg b s = return True"
          unfolding en_pos_def en_neg_def
          by (auto split: Error_Monad.bind_splits)
        thus ?thesis by (fastforce intro: cfg.intros)
      qed
  qed
qed (fastforce intro: cfg.intros)+

(* TODO: Move *)
lemma assert_simps[simp]: 
  "assert \<Phi> e = EAssert e' \<longleftrightarrow> \<not>\<Phi> \<and> e'=e"
  "assert \<Phi> e \<noteq> ENonterm"
  "assert \<Phi> e = return u \<longleftrightarrow> \<Phi>"
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
      by (metis Base En_fail Return_void True 
        `s = ((c, locals, rloc) # \<sigma>, \<gamma>, \<mu>)` assms cfg_has_enabled_action )
  next    
    case False
    from cfg_has_enabled_action[OF False] obtain c' et en tr 
      where "cfg c (et, en, tr) c' \<and> (\<not>is_return (en s) \<or> en s = return True)" by blast
    thus ?thesis proof safe
      assume "cfg c (et, en, tr) c'" "\<not>is_return (en s)"
      thus ?thesis apply - apply (rule exI) apply (rule small_step.En_fail)
      by auto
    next  
      assume A: "cfg c (et, en, tr) c'" "en s = return True"
      thus ?thesis by (force intro: small_step.Base)
    qed 
  qed
qed 

text \<open>cfg gets stuck at SKIP\<close>
lemma cfg_SKIP_stuck[simp]: "\<not> cfg SKIP a c"
  by (auto elim: cfg.cases)

text \<open>An execution is done when we can't take any more steps, this happens when the stack is empty.\<close>
lemma ss_empty_stack_stuck[simp]: "is_empty_stack s \<Longrightarrow> \<not>( s \<rightarrow> cs')"
  by (auto elim: small_step.cases)

lemma ss'_SKIP_stuck[simp]: "is_empty_stack s \<Longrightarrow> \<not>( return s \<rightarrow>' cs')"
  by (auto elim: small_step'.cases)

text \<open>the result of @{term "en_neg e s"} will always be the negation of the result of
  @{term "en_pos e s"}.\<close>
lemma en_neg_by_pos: "en_neg e s = map_error (HOL.Not) id (en_pos e s)"
  unfolding en_pos_def en_neg_def
  by (auto split: Error_Monad.bind_splits)

subsection \<open>Determinism\<close>

text \<open>We prove that cfg is deterministic.\<close>
lemma cfg_determ:
  assumes "cfg c a1 c'"
  assumes "cfg c a2 c''"
  obtains
      "a1=a2" "c' = c''"
    | b where "a1 = (ET_Intra,en_pos b,tr_eval b)" "a2 = (ET_Intra,en_neg b,tr_eval b)"
    | b where "a1 = (ET_Intra,en_neg b,tr_eval b)" "a2 = (ET_Intra,en_pos b,tr_eval b)"
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
  map_error (upd_com c) id (lift_transformer_nr tr s)"
  unfolding lift_transformer_nr_def
  by (auto split: prod.splits list.splits Error_Monad.bind_split)

text \<open>We prove that if the stack is not empty it doesn't matter if we update the command first
  and then apply the eval transformer or the other way around since the eval transformer works
  in the visible state level and doesn't temper with the command in the top of the stack.\<close>
lemma tr_eval_upd_com: "\<not>is_empty_stack s \<Longrightarrow> 
  tr_eval e (upd_com c s) = map_error (upd_com c) id (tr_eval e s)"
  unfolding tr_eval_def
  by (auto simp: lift_upd_com)

(* TODO: Move *)
lemma no_return_conv: "(\<forall>x. \<not>is_res m x) \<longleftrightarrow> (m=ENonterm) \<or> (\<exists>e. m=EAssert e)"
  by (cases m) auto

lemma [simp]: "\<not>is_empty_stack s \<Longrightarrow> (\<forall>x. \<not>is_nonterm (tr x)) \<Longrightarrow> \<not>is_nonterm (lift_transformer tr s)"
  unfolding lift_transformer_def
  by (auto split: prod.splits list.splits)

lemma [simp]: "\<not>is_nonterm (mem_get_block \<mu> addr)"
  unfolding mem_get_block_def by (auto split: prod.splits)

lemma [simp]: "\<not>is_nonterm (assert_valid_addr \<mu> addr)"
  unfolding assert_valid_addr_def by (auto split: prod.splits)

lemma [simp]: "\<not>is_nonterm (plus_val \<mu> v1 v2)"
  by (cases "(\<mu>,v1,v2)" rule: plus_val.cases) (auto simp: Let_def)

lemma [simp]: "\<not>is_nonterm (subst_val \<mu> v1 v2)"
  by (cases "(\<mu>,v1,v2)" rule: subst_val.cases) (auto simp: Let_def)

lemma [simp]: "\<not>is_nonterm (minus_val v1)"
  by (cases "(v1)" rule: minus_val.cases) auto

lemma [simp]: "\<not>is_nonterm (div_val v1 v2)"
  by (cases "(v1,v2)" rule: div_val.cases) auto

lemma [simp]: "\<not>is_nonterm (mod_val v1 v2)"
  by (cases "(v1,v2)" rule: mod_val.cases) auto

lemma [simp]: "\<not>is_nonterm (mult_val v1 v2)"
  by (cases "(v1,v2)" rule: mult_val.cases) auto

lemma [simp]: "\<not>is_nonterm (less_val \<mu> v1 v2)"
  by (cases "(\<mu>,v1,v2)" rule: less_val.cases) auto

lemma [simp]: "\<not>is_nonterm (to_bool v)"
  by (cases v rule: to_bool.cases) (auto)

lemma [simp]: "\<not>is_nonterm (not_val v1)"
  unfolding not_val_def by auto

lemma [simp]: "\<not>is_nonterm (eq_val \<mu> v1 v2)"
  by (cases "(\<mu>,v1,v2)" rule: eq_val.cases) auto

lemma [simp]: "\<not>is_nonterm (new_block v1 v2)"
  by (cases "(v1,v2)" rule: new_block.cases) auto

lemma [simp]: "\<not>is_nonterm (load v1 v2)"
  unfolding load_def
  by (auto split: prod.splits option.splits)

lemma [simp]: "\<not>is_nonterm (eval e s)" "\<not>is_nonterm (eval_l le s)"
  apply (induction e and le arbitrary: s and s)
  apply (auto split: option.splits val.splits simp: Let_def read_var_def)
  done


lemma [simp]: "\<not>is_empty_stack s \<Longrightarrow> \<not>is_nonterm (en_pos e s)"
  by (simp add: en_pos_def)

lemma [simp]: "\<not>is_empty_stack s \<Longrightarrow> \<not>is_nonterm (en_neg e s)"
  by (simp add: en_neg_def)


text \<open>We prove that small step is deterministic.\<close>
lemma small_step_determ:
  assumes "s \<rightarrow> s'"
  assumes "s \<rightarrow> s''"
  shows "s'=s''"
  using assms
  apply (cases)
  apply (erule small_step.cases)
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos tr_eval_upd_com; fail) []
  apply simp
  apply (erule (1) cfg_determ, auto simp: no_return_conv en_neg_by_pos tr_eval_upd_com; fail) []
  apply simp+

  apply (erule small_step.cases; simp?)
  apply (erule (1) cfg_determ, auto simp: no_return_conv en_neg_by_pos tr_eval_upd_com; fail) []
  apply (erule (1) cfg_determ; auto simp add: no_return_conv pw_nt_iff en_neg_by_pos; fail)

  apply (erule small_step.cases)
  apply simp+
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

context program_loc begin

text \<open>If we have a command different from SKIP and the cfg_step function returns a Base step
  as the kind of step we can take in the CFG then there will be a definition matching this in
  the cfg definition.\<close>
  lemma step_to_cfg_base: "c \<noteq> SKIP \<Longrightarrow> (cfg_step proc_table c = Base tr c') \<Longrightarrow>
      \<exists>et. cfg c (et,en_always,tr) c'"
    apply (induction c arbitrary: tr c' rule: cfg_step.induct)
    apply (auto intro: cfg.intros elim: cfg.cases split: cfg_edge.splits)
    apply (force intro: cfg.intros elim: cfg.cases split: cfg_edge.splits)
    done

lemma map_en_posneg_conv[simp]:
  "map_error HOL.Not id o en_pos e = en_neg e"
  "map_error HOL.Not id o en_neg e = en_pos e"
  unfolding en_pos_def[abs_def] en_neg_def[abs_def]
  by (auto intro!: ext split: Error_Monad.bind_splits)

text \<open>Also, if we have a command different from SKIP and the cfg_step function returns a Cond
  step as the kind of step we can take in the CFG then there will be a definition matching
  this in the cfg definition.\<close>
  lemma step_to_cfg_cond: "c \<noteq> SKIP \<Longrightarrow> (cfg_step proc_table c = Cond en tr c1' c2') \<Longrightarrow>
    (cfg c (ET_Intra,en,tr) c1' \<and> cfg c (ET_Intra,map_error HOL.Not id o en, tr) c2' )"
    apply (induction c arbitrary: tr c1' c2' rule: cfg_step.induct)
    apply (auto 
      intro: cfg.intros elim: cfg.cases split: cfg_edge.splits simp: en_neg_by_pos)
    done

text \<open>If we have a cfg rule and the first command is different from SKIP then we will always
  obtain from cfg_step a Base or a Cond step.\<close>
  lemma cfg_to_stepE:
    assumes "cfg c a c'"  
    assumes "c\<noteq>SKIP"
    obtains 
      et tr where "a = (et,en_always, tr)" "cfg_step proc_table c = Base tr c'"
    | b c2' where "a = (ET_Intra, en_pos b, tr_eval b)" "cfg_step proc_table c = Cond (en_pos b) (tr_eval b) c' c2'"
    | b c1' where "a = (ET_Intra, en_neg b, tr_eval b)" "cfg_step proc_table c = Cond (en_pos b) (tr_eval b) c1' c'"
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
definition fstep :: "proc_table \<Rightarrow> state \<hookrightarrow> state" where
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

context program_loc begin

text \<open>@{term fstep1} shows the first direction of this equality. If we can take a step in the
  small step semantics from a state s to a state s' then, executing fstep on that state s will
  yield the same s'.\<close>
  lemma fstep1: 
    assumes "s \<rightarrow> s'"  
    shows "fstep proc_table s = s'"
    using assms
    apply induction
    apply (auto simp: fstep_def)

    apply (erule cfg_to_stepE)
    apply (auto split: Error_Monad.bind_split simp: en_neg_by_pos)
    
    apply (erule cfg_to_stepE)
    apply (auto split: Error_Monad.bind_split simp: en_neg_by_pos)
    done


text \<open>@{term fstep2} shows the other direction of this equality. Assuming the stack is not
  empty then taking a step in the small step semantics from a state s will lead us to a
  to a state s' that is the result of executing fstep on that state s.\<close>
lemma fstep2: "\<not>is_empty_stack s \<Longrightarrow> s \<rightarrow> (fstep proc_table s)"
  unfolding fstep_def
  apply simp apply safe
  apply (rule small_step.Return_void; simp)

  apply (simp split: cfg_edge.splits, safe)
  apply (frule (1) step_to_cfg_base)
  apply (metis (no_types, lifting) can_take_step cfg_edge.simps(5) fstep1 fstep_def)
  apply (frule (1) step_to_cfg_cond)
  apply (auto split: Error_Monad.bind_splits)
  apply (rule small_step.En_fail, simp+) []
  apply (rule small_step.En_fail, simp+) []
  apply (rule small_step.Base, simp+) []
  apply (rule small_step.Base[where en="map_error _ _ o _"], simp+; fail) []
  done  

lemma ss_fstep_equiv: "\<not>is_empty_stack s \<Longrightarrow> s \<rightarrow> s' \<longleftrightarrow> fstep proc_table s = s'"
  using fstep1 fstep2
  by blast

end

subsection \<open>Interpreter for the semantics\<close>

text \<open>A state is considered final if the stack in that state is empty or if it's None.\<close>
fun is_term :: "state ce \<Rightarrow> bool" where
  "is_term (return s) = is_empty_stack s"
| "is_term _ = True"


text \<open>The interpreter for our semantics works as follows:
  As long as we don't reach a final state then we execute @{term fstep}.\<close>
definition interp :: "proc_table \<Rightarrow> state \<hookrightarrow> state" where
  "interp proc_table cs \<equiv> (while
    (HOL.Not o is_term)
    (\<lambda>return cs \<Rightarrow> fstep proc_table cs)
    (return cs))"

lemma interp_unfold: "interp proc_table cs = (
    if is_term (return cs) then
      return cs
    else do {
      cs \<leftarrow> fstep proc_table cs;
      interp proc_table cs
    }
  )"
  unfolding interp_def
  apply (subst while_unfold)
  apply (auto split: Error_Monad.bind_split)
  apply (subst while_unfold)
  apply auto
  apply (subst while_unfold)
  apply auto
  done

text \<open>If the state is final, it is the result of the interpretation.\<close>
lemma interp_term: "is_term (return cs) \<Longrightarrow> interp proc_table cs = return cs"
  apply (subst interp_unfold)
  by simp

subsection \<open>Correctness\<close>


context program_loc begin

text \<open>An execution of a state cs yields cs' if we can take steps from cs to cs' and cs' is
  a final state.\<close>
  definition "yields == \<lambda>cs cs'. return cs \<rightarrow>* cs' \<and> is_term cs'"
text \<open>An execution of a state cs terminates with cs' if it yields cs'.\<close>
  definition "terminates == \<lambda>cs. \<exists>cs'. yields cs cs'"

text \<open>The star operator preserves a None state. If we reach a None in our execution we will
  get stuck in a None state.\<close>
  lemma None_star_preserved[simp]: 
    assumes "\<not>is_return m"  
    shows "m \<rightarrow>* z \<longleftrightarrow> z=m"
  proof 
    assume "m \<rightarrow>* z"  
    thus "z=m"
    using assms
      apply (induction m z rule: star.induct)
      apply (auto elim!: small_step'.cases)
      done
  qed auto

text \<open>We prove that @{term small_step'} is deterministic.\<close>
  lemma small_step'_determ:
    assumes "s \<rightarrow>' s'"
    assumes "s \<rightarrow>' s''"
    shows "s'=s''"
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
    hence a: "return cs \<rightarrow>* cs'" and b: "is_term cs'" unfolding yields_def by auto
    thus "cs' = interp proc_table cs"
    proof (induction _ "return cs::_ ce" cs' arbitrary: cs rule: star.induct)
      case refl with interp_term show ?case by simp
    next
      case (step csh cs')
      from \<open>return cs \<rightarrow>'  csh\<close> have [simp]: "fstep proc_table cs = csh"
        apply (cases)
        apply (cases cs, cases csh)
        apply (auto intro: fstep1)
        done
  
      from \<open>return cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_term (return cs)" 
        apply (cases "return cs::_ ce" rule: is_term.cases)
        by auto
  
      from \<open>return cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_empty_stack cs" 
        apply (cases "return cs::_ ce" rule: is_term.cases)
        by auto

      show ?case
      proof (cases "is_return csh")
        case (True)[simp]
        then obtain cst where [simp]: "csh = return cst" by (cases csh) auto
  
        have "interp proc_table cs = interp proc_table cst"
          by (subst interp_unfold) simp
        thus ?thesis using step.hyps(3)[OF _ step.prems]
          by simp
      next
        case False with \<open>csh \<rightarrow>* cs'\<close> have [simp]: "cs'=csh" by simp
        show ?thesis using False
          apply (subst interp_unfold)
          apply (auto simp: pw_eq_iff)
          done
      qed
    qed  
  next
    from TERM obtain cs' where
      1: "return cs \<rightarrow>* cs'" "is_term cs'"
      unfolding yields_def terminates_def by auto
    hence "cs'=interp proc_table cs"
    proof (induction "return cs::_ ce" _ arbitrary: cs rule: star.induct)
      case refl thus ?case by (simp add: interp_term)
    next
      case (step csh cs')
  
      from \<open>return cs \<rightarrow>'  csh\<close> have [simp]: "fstep proc_table cs = csh"
        apply (cases)
        apply (cases cs, cases csh)
        apply (auto intro: fstep1)
        done
  
      from \<open>return cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_term (return cs)"
        apply (cases "return cs::_ ce" rule: is_term.cases)
        by auto

      from \<open>return cs \<rightarrow>'  csh\<close> have [simp]: "\<not>is_empty_stack cs"
        apply (cases "return cs :: _ ce" rule: is_term.cases)
        by auto
  
      show ?case
      proof (cases "is_return csh")
        case False
        with \<open>csh \<rightarrow>* cs'\<close> have [simp]: "cs'=csh" by simp
        show ?thesis using False
          by (subst interp_unfold) (auto simp: pw_eq_iff)
      next
        case True then obtain cst where [simp]: "csh=return cst" by (cases csh) auto
  
        have "interp proc_table cs = interp proc_table cst"
          by (subst interp_unfold) simp
        thus ?thesis using step.hyps(3)[OF _ step.prems]
          by simp
      qed
    qed
    with 1 have "return cs \<rightarrow>* interp proc_table cs" "is_term (interp proc_table cs)" by simp_all
    thus "yields cs (interp proc_table cs)" by (auto simp: yields_def)
  qed



lemmas [code] = interp_unfold

export_code interp checking SML


end

subsection \<open>Execution of a program\<close>

text \<open>In order to execute a program we will assert that it's valid following the previously
  defined @{term valid_program} definition, and proceed to interpret the initial state of the
  program p.\<close>
definition execute :: "program \<hookrightarrow> state" where
  "execute p \<equiv> do {
    assert (program_loc.wt_prog p) (EChecker EWf);
    interp (proc_table_of p) (program_loc.initial_state p)
  }"


(*
  interpretation program_loc__!: program_loc p for p .
  interpretation stackframe__!: stackframe p fd for p fd .

  export_code execute checking SML
*)


end

