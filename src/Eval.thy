theory Eval
imports Com Exp 
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Code_Target_Nat"
  "Native_Word/Word_Misc" (* For signed div and signed mod *)
begin
section \<open>Eval\<close>

subsection \<open>Type definitions\<close>

text \<open>A value in the semantics can be a Null value, an integer or an address.\<close>
datatype val = NullVal | I int_val | A addr

(*
  A state is a pair in which the first element represents the content of the local variables
  and the second element represents the content of the blocked memory.
  The memory is organized in blocks and it is accesed with the address of the block and the index
  of the block we want to access. The memory is encoded as a list of blocks, and each block is
  a list of values.
  state = (\<sigma>, \<mu>) \<sigma>: content of local variables, \<mu>: content of memory
*)

text \<open>A return location for a function can be an address, a variable or Invalid. It's invalid
  in the case when the function returns void.\<close>
datatype return_loc = Ar addr | Vr vname | Invalid


text \<open>A valuation is a function that maps a variable name to value. The valuation of a variable
  name is of type @{term "val option option"}.
  If the valuation of variable returns None, it means that the variable is undefined.
  If the valuation of variable returns Some None, it means that the variable is uninitialized.
  If the valuation of variable returns Some <value>, it means that the content of the variable
  is <value>.
\<close>
type_synonym valuation = "vname \<Rightarrow> val option option"

text \<open>The dynamic memory is represented by a @{term "val option list option list"}.
  The memory is represented by blocks allocated with @{term New}.
  We index the memory with the address value, an address is a pair of (base, offset), we index the
  list with the base that identifies the block. If the block is not allocated, when indexing the
  list in the base position there will be a None value, if the block is allocated then there's a
  Some list that denotes the content of the block. We use the offset to index inside the block.
  If the cell in the block we try to index is uninitialized there will be a None value, otherwise
  there will be a Some None indicating an uninitialized value, and a Some <value> for an initialized cell
  with content <value>.\<close>
type_synonym mem = "val option list option list"

text \<open>We define a stack frame for procedure calls as the command we must execute, the valuation for
  the locals in that particular stack frame and the return location in which a caller will expect
  the result of a function call. The caller saves the return location in it's own stack frame.\<close>
type_synonym stack_frame = "com \<times> valuation \<times> return_loc"

text \<open>A state is formed by a stack, a valuation for globals and the dynamic memory.\<close>
type_synonym state = "stack_frame list \<times> valuation \<times> mem"

text \<open>When executing a command that's not a function call or a return, this command won't make any
  changes in the stack, therefore it only needs the valuation for the locals, the valuation for the
  globals and the dynamic memory to be executed. In a visible state there's no possibility that the
  evaluation of a command modifies the stack since the stack is not available to it.\<close>
type_synonym visible_state = "valuation \<times> valuation \<times> mem"

text \<open>We then lift the transformations done at a visible state level to states.
  Here we separate the locals valuation from the rest of the stack frame, apply the transformation
  to the visible state and then reconstruct the complete state with the part of the stack frame the
  transformer didn't need in order to be executed, namely the command, and the return location.
  This way we can now execute transformers at a state level. Applying the transformer will yield a
  result, we also yield this result with the state in the end.\<close>
definition lift_transformer :: 
  "(visible_state \<rightharpoonup> ('a\<times>visible_state))
  \<Rightarrow> state \<rightharpoonup> ('a \<times> state)"
where
  "lift_transformer tr \<equiv> \<lambda>s. case s of((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> do {
    (r,(lvars,\<gamma>,\<mu>)) \<leftarrow> tr (lvars,\<gamma>,\<mu>);
    Some (r,((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>))
  }"

text \<open>This is the lift of the transformations done at a visible state level to states.
  The difference between this lift and @{term lift_transformer} is that the transformer executed
  in here doesn't return a value, then we return just the state in the end.\<close>
definition lift_transformer_nr 
  :: "(visible_state \<rightharpoonup> (visible_state)) \<Rightarrow> state \<rightharpoonup> (state)"
where
  "lift_transformer_nr tr \<equiv> \<lambda>((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> do {
    (lvars,\<gamma>,\<mu>) \<leftarrow> tr (lvars,\<gamma>,\<mu>);
    Some (((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>))
  }"

definition is_empty_stack :: "state \<Rightarrow> bool" where
  "is_empty_stack \<equiv> \<lambda>(\<sigma>,_,_). \<sigma>=[]"

lemma is_empty_stack_prod_conv[simp]: "is_empty_stack (\<sigma>,\<mu>\<gamma>) \<longleftrightarrow> \<sigma>=[]"
  unfolding is_empty_stack_def by auto

fun com_of :: "state \<Rightarrow> com" where
  "com_of ((com,_)#_,_,_) = com"

fun upd_com :: "com \<Rightarrow> state \<Rightarrow> state" where
  "upd_com com ((_,l)#\<sigma>,\<gamma>,\<mu>) = ((com,l)#\<sigma>,\<gamma>,\<mu>)"

fun coms_of_state :: "state \<Rightarrow> com set" where
  "coms_of_state (\<sigma>,_) = (\<lambda>(com,_). com)`set \<sigma>"

definition coms_of_stack :: "stack_frame list \<Rightarrow> com set" where
  "coms_of_stack \<sigma> \<equiv> (\<lambda>(com,_). com)`set \<sigma>"

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

abbreviation "list_size xs \<equiv> int(length xs)"

text \<open>We're using signed longs in the translation to C, this are the min, and max values that it's
  possible to represent with signed longs.\<close>
abbreviation "INT_MIN \<equiv> -2147483647" (* 64 bits, signed long *)
abbreviation "INT_MAX \<equiv>  2147483647" (* 64 bits, signed long *)

text \<open>In the C99 draft, integer overflow is undefined behaviour, therefore we detect overflow and
  then return None if overflow occurs and then the execution of the semantics goes to error.\<close>
fun detect_overflow :: "int \<Rightarrow> val option" where
  "detect_overflow i = (if (i > INT_MIN \<and> i \<le> INT_MAX) then Some (I (word_of_int i)) else None)"

value "detect_overflow (INT_MAX + 1)"
value "detect_overflow (INT_MIN - 1)"

text \<open>We define addition for values, according to the C99 draft we can add two integers or a
  pointer value and an integer.\<close>
fun plus_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "plus_val (I i\<^sub>1) (I i\<^sub>2) = detect_overflow (sint i\<^sub>1 + sint i\<^sub>2)"
| "plus_val (A (x,y)) (I i) = do {
    v \<leftarrow> detect_overflow (y + sint i);
    (case v of (I offset) \<Rightarrow> Some (A (x, sint offset)) | _ \<Rightarrow> None)
  }"
| "plus_val a\<^sub>1 a\<^sub>2 = None"

(* Maybe check this is doing the right thing *)
text \<open>We define substraction for values, according to the C99 draft we can substract an integer
  from another or a pointer value and an integer. C99 draft also allows substraction between two
  pointers, this semantics doesn't allow that.\<close>
fun subst_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "subst_val (I i\<^sub>1) (I i\<^sub>2) = detect_overflow (sint i\<^sub>1 - sint i\<^sub>2)"
| "subst_val (A (x,y)) (I i) = do {
    v \<leftarrow> detect_overflow (y - sint i);
    (case v of (I offset) \<Rightarrow> Some (A (x, sint offset)) | _ \<Rightarrow> None)
  }"
| "subst_val a\<^sub>1 a\<^sub>2 = None"

text \<open>We define unary minus for values. It detects overflow and returns None if it happens.\<close>
fun minus_val :: "val \<Rightarrow> val option" where
  "minus_val (I i) = detect_overflow (- (sint i))"
| "minus_val a = None"

(* Add overflow check on div and mod? *)
text \<open>@{term "op sdiv"} implements truncation towards zero, 
  conforming to the C99 standard, Sec. 6.5.5/6\<close>
fun div_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "div_val (I i\<^sub>1) (I i\<^sub>2) = (if (i\<^sub>2 \<noteq> 0) then Some (I (i\<^sub>1 sdiv i\<^sub>2)) else None)"
| "div_val a\<^sub>1 a\<^sub>2 = None"

fun mod_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "mod_val (I i\<^sub>1) (I i\<^sub>2) = (if (i\<^sub>2 \<noteq> 0) then Some (I (i\<^sub>1 smod i\<^sub>2)) else None)"
| "mod_val a\<^sub>1 a\<^sub>2 = None"

fun mult_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "mult_val (I i\<^sub>1) (I i\<^sub>2) = detect_overflow (sint i\<^sub>1 * sint i\<^sub>2)"
| "mult_val a\<^sub>1 a\<^sub>2 = None"

text \<open>We define the less than operator for values, if the first value is smaller than the second we
  return @{term "I 1"} for True, otherwise we return @{term "I 0"} for False.\<close>
fun less_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "less_val (I i\<^sub>1) (I i\<^sub>2) = (if i\<^sub>1 <s i\<^sub>2 then Some (I 1) else Some (I 0))"
| "less_val a\<^sub>1 a\<^sub>2 = None"

text \<open>We define the not operator for values, if the value is 0 (False) we return @{term "I 1"} for
  True, otherwise we return @{term "I 0"} for False.\<close>
fun not_val :: "val \<Rightarrow> val option" where
  "not_val (I i) = (if i = 0 then Some (I 1) else Some (I 0))"
| "not_val a = None"

fun and_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "and_val (I i\<^sub>1) (I i\<^sub>2) = (if i\<^sub>1 = 0 then Some (I 0) else (if i\<^sub>2 = 0 then Some (I 0) else Some (I 1)))"
| "and_val a\<^sub>1 a\<^sub>2 = None"

fun eq_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "eq_val (I i\<^sub>1) (I i\<^sub>2) = (if i\<^sub>1 = i\<^sub>2 then Some (I 1) else Some (I 0))"
| "eq_val (A (i\<^sub>1,j\<^sub>1)) (A (i\<^sub>2,j\<^sub>2)) = (if i\<^sub>1 = i\<^sub>2 \<and> j\<^sub>1 = j\<^sub>2 then Some (I 1) else Some (I 0))"
| "eq_val a\<^sub>1 a\<^sub>2 = None"

value "eq_val (I 5) (I 6)"
value "eq_val (I 5) (I 5)"
value "eq_val (A (0,1)) (A (6,5))"
value "eq_val (A (0,1)) (A (0,5))"
value "eq_val (A (6,5)) (A (6,5))"
value "eq_val (I 1) (A (6,5))"

(* Allocates a new block in the memory *)
(* n
  This is using conversions between int and nat I don't know what happens if the number in 
  (I i) is neg
*)
fun new_block :: "val \<Rightarrow> mem \<Rightarrow> (val \<times> mem) option" where
  "new_block (I i) \<mu> = (
    if sint i < 0 then None
    else
      Some ((A (length \<mu>, 0)), \<mu> @ [ Some (replicate (nat (sint i)) None)])
  )"
| "new_block _ _ = None"

value "new_block (I 2) [Some []]"

fun valid_mem :: "addr \<Rightarrow> mem \<Rightarrow> bool" where
  "valid_mem (i,j) \<mu> = (
    if i<length \<mu> then (
      case \<mu>!i of
        None \<Rightarrow> False
      | Some b \<Rightarrow> 0\<le>j \<and> nat j < length b)
    else False)"

fun ofs_addr :: "addr \<Rightarrow> int_val \<Rightarrow> addr" where
  "ofs_addr (i,j) ofs = (i,j + sint ofs)"

definition load :: "addr \<Rightarrow> mem \<Rightarrow> val option" where
  "load \<equiv> \<lambda>(i,j) \<mu>.
    if valid_mem (i,j) \<mu> then do {
      v \<leftarrow> (the (\<mu>!i) !! j);  (* Yields None if memory location is uninitialized *)
      Some v
    } else
      None"

definition store :: "addr \<Rightarrow> val \<Rightarrow> visible_state \<Rightarrow> visible_state option"
   where
  "store \<equiv> \<lambda>(i,j) v (l,\<gamma>,\<mu>).
    if valid_mem (i,j) \<mu> then
      Some (l,\<gamma>,\<mu>[i := Some ( the (\<mu>!i) [nat j := Some v] )])
    else
      None"

definition free :: "addr \<Rightarrow> visible_state \<Rightarrow> visible_state option" where
  "free \<equiv>  \<lambda>(i,j) (l,\<gamma>,\<mu>).
    if valid_mem (i,j) \<mu> then
      Some (l,\<gamma>,\<mu>[i := None])
    else
      None"

(*
  The return here is a pair (val \<times> state) option. The state is necessary because malloc and free
  are expressions and those modify the state. We treat this as an option because None would be
  a special error state in which the evaluation got stuck i.e. sum of two pointers.
*)

definition "assert \<Phi> \<equiv> if \<Phi> then Some () else None"

fun read_var :: "vname \<Rightarrow> visible_state \<Rightarrow> val option" where
  "read_var x (l,\<gamma>,\<mu>) = do {
    case l x of
      Some v \<Rightarrow> v
    | None \<Rightarrow> do {
        case \<gamma> x of
          Some v \<Rightarrow> v
        | None \<Rightarrow> None  
      } 
  }"

fun write_var :: "vname \<Rightarrow> val \<Rightarrow> visible_state \<Rightarrow> visible_state option" where
  "write_var x v (l,\<gamma>,\<mu>) = do {
    case l x of
      Some _ \<Rightarrow> do {
        let l = l (x \<mapsto> Some v);
        Some (l,\<gamma>,\<mu>)
      }
    | None \<Rightarrow> do {
        assert (\<gamma> x \<noteq> None);
        let \<gamma> = \<gamma>(x \<mapsto> Some v);
        Some (l,\<gamma>,\<mu>)
      }
  }"


fun eval :: "exp \<Rightarrow> visible_state \<Rightarrow> (val \<times> visible_state) option"
and eval_l :: "lexp \<Rightarrow> visible_state \<Rightarrow> (addr \<times> visible_state) option" where
  "eval (Const c) s = Some (I c, s)"
| "eval Null s = Some (NullVal, s)"
| "eval (V x) s = do {
    v \<leftarrow> read_var x s;
    Some (v, s)
    }"
| "eval (Plus i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> plus_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (Subst i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> subst_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (Minus i) s = do {
  (v, s) \<leftarrow> eval i s;
  v \<leftarrow> minus_val v;
  Some (v, s)
}"
| "eval (Div i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> div_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (Mod i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> mod_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (Mult i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> mult_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (Less i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> less_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (Not b) s = do {
  (v, s) \<leftarrow> eval b s;
  v \<leftarrow> not_val v;
  Some (v, s)
}"
| "eval (And b\<^sub>1 b\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval b\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval b\<^sub>2 s;
  v \<leftarrow> and_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
(* p \<or> q \<equiv> \<not>(\<not> p \<and> \<not>q)*)
| "eval (Or b\<^sub>1 b\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval b\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval b\<^sub>2 s;
  v\<^sub>1 \<leftarrow> not_val v\<^sub>1;
  v\<^sub>2 \<leftarrow> not_val v\<^sub>2;
  v \<leftarrow> and_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (Eq e\<^sub>1 e\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval e\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval e\<^sub>2 s;
  v \<leftarrow> eq_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"
| "eval (New e) s = do {
  (v, (l, \<gamma>, \<mu>)) \<leftarrow> eval e s;
  (v, \<mu>) \<leftarrow> new_block v \<mu>;
  Some (v, (l, \<gamma>, \<mu>))
}"
| "eval (Deref e) s = do {
  (v, (l, \<gamma>, \<mu>)) \<leftarrow> eval e s;
  case v of
    (A addr) \<Rightarrow> do {
      v \<leftarrow> load addr \<mu>;
      Some (v, (l, \<gamma>, \<mu>))
    }
  | _ \<Rightarrow> None
}"
| "eval (Ref e) s = (case (eval_l e s) of
                       None \<Rightarrow> None |
                       Some (addr, s) \<Rightarrow> Some (A addr,s))"
| "eval (Index e\<^sub>1 e\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval e\<^sub>1 s;
  (v\<^sub>2, (l, \<gamma>, \<mu>)) \<leftarrow> eval e\<^sub>2 s;
  case (v\<^sub>1, v\<^sub>2) of
    (A addr, I incr) \<Rightarrow> do {
      v \<leftarrow> load (ofs_addr addr incr) \<mu>;
      Some (v, (l, \<gamma>, \<mu>))
    }
  | _ \<Rightarrow> None
}"
| "eval_l (Derefl e) s = do {
    (v,s) \<leftarrow> eval e s;
    case v of A addr \<Rightarrow> Some (addr,s)
    | _ \<Rightarrow> None
  }"
| "eval_l (Indexl e\<^sub>1 e\<^sub>2) s = do {
    (v\<^sub>1,s) \<leftarrow> eval e\<^sub>1 s;
    (v\<^sub>2,s) \<leftarrow> eval e\<^sub>2 s;
    case (v\<^sub>1,v\<^sub>2) of
      (A (base,ofs), I incr) \<Rightarrow> Some ((base,ofs+sint incr),s)
    | _ \<Rightarrow> None
  }"


export_code eval checking SML

end

