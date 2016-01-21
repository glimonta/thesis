theory Eval
imports Com Exp 
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Code_Target_Nat"
  Error_Monad
  "Native_Word/Word_Misc" (* For signed div and signed mod *)
begin

datatype static_error -- \<open>Errors that should be detected statically\<close>
  = 
    EType       -- \<open>Type error\<close>
  | EStructure  -- \<open>Structural error\<close>
datatype dynamic_error = 
    EOverflow       -- \<open>Over or underflow\<close>
  | EDivZero        -- \<open>Division by zero\<close>
  | EPtr            -- \<open>Invalid address\<close>
  | EUninitialized  -- \<open>Uninitialized value\<close>
datatype wf_error -- \<open>Static checkers\<close>
  =
    ETypeChecker    -- \<open>Type checker\<close>
  | EWf             -- \<open>Well-formedness checks\<close>

datatype chloe_error = 
  is_EStatic: EStatic static_error 
| is_EDynamic: EDynamic dynamic_error 
| is_EChecker: EChecker wf_error

abbreviation "type_error \<equiv> EAssert (EStatic EType)"
abbreviation "overflow_error \<equiv> EAssert (EDynamic EOverflow)"
abbreviation "div_zero_error \<equiv> EAssert (EDynamic EDivZero)"
abbreviation "pointer_error \<equiv> EAssert (EDynamic EPtr)"
abbreviation "uninitalized_error \<equiv> EAssert (EDynamic EUninitialized)"
abbreviation "structural_error \<equiv> EAssert (EStatic EStructure)"

type_synonym ('a) ce = "('a,chloe_error) error"
type_synonym ('a,'b) cefun = "'a \<Rightarrow> 'b ce"

type_notation cefun (infixr "\<hookrightarrow>" 0)

section \<open>Eval\<close>

subsection \<open>Type definitions\<close>

text \<open>A value in the semantics can be a Null value, an integer, an address, or a structure value.
  A structure can be uninitialized field-wise, uninitialized fields are represented 
  as @{text "Some None"}.
\<close>
datatype val = NullVal | I int_val | A addr | SVal "(vname \<times> val option) list"

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

subsection \<open>Auxiliary functions to handle states\<close>

text \<open>We then lift the transformations done at a visible state level to states.
  Here we separate the locals valuation from the rest of the stack frame, apply the transformation
  to the visible state and then reconstruct the complete state with the part of the stack frame the
  transformer didn't need in order to be executed, namely the command, and the return location.
  This way we can now execute transformers at a state level. Applying the transformer will yield a
  result, we also yield this result with the state in the end.\<close>

definition lift_transformer :: 
  "(visible_state \<hookrightarrow> ('a\<times>visible_state))
  \<Rightarrow> state \<hookrightarrow> ('a \<times> state)"
where
  "lift_transformer tr \<equiv> \<lambda>s. case s of((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> do {
    (r,(lvars,\<gamma>,\<mu>)) \<leftarrow> tr (lvars,\<gamma>,\<mu>);
    return (r,((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>))
  }"

text \<open>This is the lift of the transformations done at a visible state level to states.
  The difference between this lift and @{term lift_transformer} is that the transformer executed
  in here doesn't return a value, then we return just the state in the end.\<close>
definition lift_transformer_nr 
  :: "(visible_state \<hookrightarrow> (visible_state)) \<Rightarrow> state \<hookrightarrow> (state)"
where
  "lift_transformer_nr tr \<equiv> \<lambda>((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> do {
    (lvars,\<gamma>,\<mu>) \<leftarrow> tr (lvars,\<gamma>,\<mu>);
    return (((com,lvars,rloc)#\<sigma>,\<gamma>,\<mu>))
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

(*fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"*)

abbreviation "list_size xs \<equiv> int(length xs)"

subsection \<open>Auxiliary functions to handle evaluations\<close>

text \<open>In the C99 draft, integer overflow is undefined behaviour, therefore we detect overflow and
  then return None if overflow occurs and then the execution of the semantics goes to error.\<close>
fun detect_overflow :: "int \<hookrightarrow> val" where
  "detect_overflow i = do {
    assert (INT_MIN \<le> i \<and> i \<le> INT_MAX) (EDynamic EOverflow); 
    return (I (word_of_int i))
  }"

value "detect_overflow (INT_MAX + 1)"
value "detect_overflow (INT_MIN - 1)"

text \<open>
  In C99/Sec 6.5.7, operations on pointers are only defined if the pointers
  point inside an array, or one element past the array.
  There are some exceptions for pointer subtraction 6.5.6.9, which we do 
  not support here (i.e., we go to undefined).

  The following functions check whether a pointer is valid.
\<close>

definition mem_get_block :: "mem \<Rightarrow> nat \<hookrightarrow> val option list" where
  "mem_get_block \<mu> i \<equiv> do {
    assert (i<length \<mu>) (EDynamic EPtr);
    assert (\<mu>!i \<noteq> None) (EDynamic EPtr);
    return (the (\<mu>!i))
  }"


definition assert_valid_addr :: "mem \<Rightarrow> addr \<hookrightarrow> unit" where
  "assert_valid_addr \<mu> \<equiv> \<lambda>(i,j). do {
    b \<leftarrow> mem_get_block \<mu> i;
    assert (j\<ge>0 \<and> j\<le>int (length b)) (EDynamic EPtr)
  }"

text \<open>Verifies if an address is in the allocated memory range.\<close>
definition valid_mem :: "addr \<Rightarrow> mem \<Rightarrow> bool" where
  "valid_mem \<equiv> \<lambda>(i,j) \<mu>. (
    if i<length \<mu> then (
      case \<mu>!i of
        None \<Rightarrow> False
      | Some b \<Rightarrow> 0\<le>j \<and> nat j < length b)
    else False)"

fun ofs_addr :: "mem \<Rightarrow> addr \<Rightarrow> int_val \<hookrightarrow> addr" where
  "ofs_addr \<mu> (i,j) ofs = do {
    assert_valid_addr \<mu> (i,j);
    let j = j + sint ofs;
    assert_valid_addr \<mu> (i,j);
    return (i,j)
}"

text \<open>We define addition for values, according to the C99 draft we can add two integers or a
  pointer value and an integer.\<close>
fun plus_val :: "mem \<Rightarrow> val \<Rightarrow> val \<hookrightarrow> val" where
  "plus_val _ (I i\<^sub>1) (I i\<^sub>2) = detect_overflow (sint i\<^sub>1 + sint i\<^sub>2)"
| "plus_val \<mu> (A addr) (I ofs) = do { addr \<leftarrow> ofs_addr \<mu> addr ofs; return (A addr) }"
| "plus_val _ NullVal (I _) = pointer_error"
| "plus_val _ _ _ = type_error"

text \<open>We define substraction for values, according to the C99 draft we can substract an integer
  from another or a pointer value and an integer. \<close>
fun subst_val :: "mem \<Rightarrow> val \<Rightarrow> val \<hookrightarrow> val" where
  "subst_val _ (I i\<^sub>1) (I i\<^sub>2) = detect_overflow (sint i\<^sub>1 - sint i\<^sub>2)"
| "subst_val \<mu> (A (i,j)) (I ofs) = do {
    assert_valid_addr \<mu> (i,j);
    let j = j - sint ofs;
    assert_valid_addr \<mu> (i,j);
    return (A (i,j))
  }"
| "subst_val _ NullVal (I _) = pointer_error"
| "subst_val \<mu> (A (i\<^sub>1,j\<^sub>1)) (A (i\<^sub>2,j\<^sub>2)) = do {
    assert_valid_addr \<mu> (i\<^sub>1,j\<^sub>1);
    assert_valid_addr \<mu> (i\<^sub>2,j\<^sub>2);
    assert (i\<^sub>1=i\<^sub>2) (EDynamic EPtr);
    detect_overflow (j\<^sub>1 - j\<^sub>2)
  }"
| "subst_val _ NullVal NullVal = pointer_error"
| "subst_val _ NullVal (A _) = pointer_error"
| "subst_val _ (A _) NullVal = pointer_error"
| "subst_val _ a\<^sub>1 a\<^sub>2 = type_error"

text \<open>We define unary minus operator for values conforming to the C99 Standard Sec. 6.5.3.3.3.
  It detects overflow and returns None if it happens.\<close>
fun minus_val :: "val \<hookrightarrow> val" where
  "minus_val (I i) = detect_overflow (- (sint i))"
| "minus_val a = type_error"

text \<open>Integer division with truncation towards zero, 
  conforming to the C99 standard, Sec. 6.5.5/6\<close>
definition div_towards_zero :: "int \<Rightarrow> int \<Rightarrow> int" where
  "div_towards_zero a b \<equiv> (\<bar>a\<bar> div \<bar>b\<bar>) * sgn a * sgn b"

text \<open>Integer modulo with truncation towards zero, 
  conforming to the C99 standard, Sec. 6.5.5/6\<close>
definition mod_towards_zero :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mod_towards_zero a b \<equiv> a - (div_towards_zero a b) * b "

text \<open>The C99 standard, Sec. 6.5.5/6 states that "If the quotient a/b is representable,
  the expression (a/b)*b + a%b shall equal a"\<close>
lemma div_mod_conform_to_c99: 
  "div_towards_zero a b * b + mod_towards_zero a b = a"
  unfolding mod_towards_zero_def by auto

text \<open>We define integer division conforming to the C99 standard and check for overflow.
  Division can only happen between two integers. Division by zero is checked and will
  yield a None val which means it's an error in our semantics.\<close>
fun div_val :: "val \<Rightarrow> val \<hookrightarrow> val" where
  "div_val (I i\<^sub>1) (I i\<^sub>2) = (
    if (i\<^sub>2 \<noteq> 0) then 
      detect_overflow (div_towards_zero (sint i\<^sub>1) (sint i\<^sub>2)) 
    else div_zero_error)"
| "div_val a\<^sub>1 a\<^sub>2 = type_error"

text \<open>We define integer modulo conforming to the C99 standard and check for overflow.
  Modulo can only happen between two integers. Modulo by zero is checked and will
  yield a None val which means it's an error in our semantics.\<close>
fun mod_val :: "val \<Rightarrow> val \<hookrightarrow> val" where
  "mod_val (I i\<^sub>1) (I i\<^sub>2) = (
    if (i\<^sub>2 \<noteq> 0) then 
      detect_overflow (mod_towards_zero (sint i\<^sub>1) (sint i\<^sub>2)) 
    else div_zero_error)"
| "mod_val a\<^sub>1 a\<^sub>2 = type_error"

text \<open>We define integer multiplication conforming to the C99 standard.
  Multiplication can only occur for integer values, we check for overflow, in case there
  is overflow then we go to an error state.\<close>
fun mult_val :: "val \<Rightarrow> val \<hookrightarrow> val" where
  "mult_val (I i\<^sub>1) (I i\<^sub>2) = detect_overflow (sint i\<^sub>1 * sint i\<^sub>2)"
| "mult_val a\<^sub>1 a\<^sub>2 = type_error"

text \<open>We define the less than operator for values conforming to the C99 standard Sec. 6.5.8.6,
  if the first value is smaller than the second it yields @{term "I 1"} for True,
  otherwise it yields @{term "I 0"} for False. \<close>

fun to_bool :: "val \<hookrightarrow> bool" where
  "to_bool (I i) = return (i\<noteq>0)"
| "to_bool _ = type_error"

abbreviation (input) false_val :: val where "false_val \<equiv> I 0"
abbreviation (input) true_val :: val where "true_val \<equiv> I 1"

definition from_bool :: "bool \<Rightarrow> val" where
  "from_bool b \<equiv> if b then true_val else false_val"

fun less_val :: "mem \<Rightarrow> val \<Rightarrow> val \<hookrightarrow> val" where
  "less_val _ (I i\<^sub>1) (I i\<^sub>2) = return (from_bool (i\<^sub>1 <s i\<^sub>2))"
| "less_val \<mu> (A (i\<^sub>1,j\<^sub>1)) (A (i\<^sub>2,j\<^sub>2)) = do {
    assert_valid_addr \<mu> (i\<^sub>1,j\<^sub>1);
    assert_valid_addr \<mu> (i\<^sub>2,j\<^sub>2);
    assert (i\<^sub>1 = i\<^sub>2) (EDynamic EPtr);
    return (from_bool (j\<^sub>1 < j\<^sub>2))
}"
| "less_val _ (A _) (NullVal) = pointer_error"
| "less_val _ (NullVal) (A _) = pointer_error"
| "less_val _ (NullVal) (NullVal) = pointer_error"
| "less_val _ a\<^sub>1 a\<^sub>2 = type_error"

thm less_val.simps

text \<open>We define the logical negation operator for values conforming to the C99 Standard
  Sec. 6.5.3.3.5, if the value is compares equal to @{term "I 0"} (False) we return
  @{term "I 1"} for True, otherwise we return @{term "I 0"} for False.
  Only integers can be compared.\<close>
definition not_val :: "val \<hookrightarrow> val" where "not_val v \<equiv> do {
  b \<leftarrow> to_bool v;
  return (from_bool (\<not>b))
}"

text \<open>We define the logical AND operator, conforming to the C99 Standard Sec. 6.5.13.3/4.
  if both operands compare unequal to @{term "I 0"} (both operands are True) then it yields @{term "I 1"}
  for True, otherwise it yields @{term "I 0"} for False. It guarantees left-to-right
  short-circuit evaluation; if the first operand compares equal to @{term "I 0"} then the
  second operand is not evaluated and @{term "I 0"} is yielded. AND operator can only operate
  between two integers.\<close>


text \<open>We define the logical OR operator, conforming to the C99 Standard Sec. 6.5.14.3/4.
  if either of its operands compare unequal to @{term "I 0"} (either operand is True)
  then it yields @{term "I 1"} for True, otherwise it yields @{term "I 0"} for False.
  It guarantees left-to-right short-circuit evaluation; if the first operand compares
  equal to @{term "I 1"} then the second operand is not evaluated and @{term "I 1"} is
  yielded. OR operator can only operate between two integers.\<close>


text \<open>We define the equal operator for values conforming to the C99 standard Sec. 6.5.9.3,
  if both values are equal it yields @{term "I 1"} for True, otherwise it yields
  @{term "I 0"} for False. Both two integer values or two address values can be compared,
  but comparing an integer and an address will lead to error. When comparing two addresses
  these fulfill the equality relation if both the base of the block and the offset of the block
  is equal in the values, or if both are the null pointer.
  Note that we resort to undefined behaviour if one or both
  of the pointers point to an object that has already been freed. The C99 standard Sec. 6.5.9 is
  not completely clear here.
\<close>

fun eq_val :: "mem \<Rightarrow> val \<Rightarrow> val \<hookrightarrow> val" where
  "eq_val _ (I i\<^sub>1) (I i\<^sub>2) = (if i\<^sub>1 = i\<^sub>2 then return true_val else return false_val)"
| "eq_val \<mu> (A (i\<^sub>1,j\<^sub>1)) (A (i\<^sub>2,j\<^sub>2)) = do {
    assert_valid_addr \<mu> (i\<^sub>1,j\<^sub>1);
    assert_valid_addr \<mu> (i\<^sub>2,j\<^sub>2);
    (if i\<^sub>1 = i\<^sub>2 \<and> j\<^sub>1 = j\<^sub>2 then return true_val else return false_val)
    }" 
| "eq_val \<mu> (A (i,j)) (NullVal) = do {assert_valid_addr \<mu> (i,j); return false_val}"
| "eq_val \<mu> (NullVal) (A (i,j)) = do {assert_valid_addr \<mu> (i,j); return false_val}"
| "eq_val _ (NullVal) (NullVal) = return true_val"
| "eq_val _ a\<^sub>1 a\<^sub>2 = type_error"

value "eq_val \<mu> (I 5) (I 6)"
value "eq_val \<mu> (I 5) (I 5)"
value "eq_val \<mu> (A (0,1)) (A (6,5))"
value "eq_val \<mu> (A (0,1)) (A (0,5))"
value "eq_val \<mu> (A (6,5)) (A (6,5))"
value "eq_val \<mu> (I 1) (A (6,5))"

(* TODO: Add regression for comparison of pointers and null pointer! *)

(* Allocates a new block in the memory *)
(* n
  This is using conversions between int and nat I don't know what happens if the number in 
  (I i) is neg
*)
text \<open>We define a function @{term new_block} that allocates a new block in the memory.
  a new block of size @{term "I i"} is allocated in memory. The list containing the memory
  representation will increase in size and the function will return a pair with the value of
  the address where the new block starts and the updated memory with the new block allocated.
  An allocation of a new block will always be successful unless the size is less or equal than
  @{term "I 0"} or if the value used as an argument is different from an integer, i.e. an address.
  The C99 Standard Sec. 7.20.3 states that "If the size of the space requested is zero, the
  behavior is implementation defined" therefore we don't allow the allocation of a new block of
  size 0.\<close>
fun new_block :: "val \<Rightarrow> mem \<hookrightarrow> (val \<times> mem)" where
  "new_block (I i) \<mu> = (
    if sint i \<le> 0 then overflow_error
    else
      return ((A (length \<mu>, 0)), \<mu> @ [ Some (replicate (nat (sint i)) None)])
  )"
| "new_block _ _ = type_error"

value "new_block (I 1) [Some [Some (I 0)]]"
value "new_block (I 0) [Some [None]]"

subsection \<open>Auxiliary functions to handle memory evaluations\<close>


text \<open>Loads the content of an address. Checks if we try to access a valid address in the memory
  and proceeds to return the value of the memory location in this address. It will yield None
  if the memory location is not initialized.\<close>
definition load :: "addr \<Rightarrow> mem \<hookrightarrow> val" where
  "load \<equiv> \<lambda>(i,j) \<mu>.
    if valid_mem (i,j) \<mu> then 
      case the (\<mu>!i) ! (nat j) of
        Some v \<Rightarrow> return v
      | None \<Rightarrow> uninitalized_error
    else
      pointer_error"

text \<open>Stores a value in the memory location indicated by the address. It checks if we try to
  access a valid address in the memory and proceeds to save the value in this memory location.
  This works in the @{term visible_state} level since the execution stack won't get modificated
  by a store operation. None will be yielded if the memory location to which we want to store
  a value is invalid.\<close>
definition store :: "addr \<Rightarrow> val \<Rightarrow> visible_state \<hookrightarrow> visible_state"
   where
  "store \<equiv> \<lambda>(i,j) v (l,\<gamma>,\<mu>).
    if valid_mem (i,j) \<mu> then
      return (l,\<gamma>,\<mu>[i := Some ( the (\<mu>!i) [nat j := Some v] )])
    else
      pointer_error"

text \<open>Deallocates the memory block indicated by the address. It checks if we try to
  deallocate a valid address in the memory and proceeds to leave a @{term None} value in the
  address of the block to indicate this memory is deallocated. This works in the
  @{term visible_state} level since the execution stack won't get modificated by a free
  operation. None will be yielded if the memory location we want to deallocate is invalid.\<close>
definition free :: "addr \<Rightarrow> visible_state \<hookrightarrow> visible_state" where
  "free \<equiv>  \<lambda>(i,j) (l,\<gamma>,\<mu>). do {
    assert_valid_addr \<mu> (i,j);
    assert (j=0) (EDynamic EPtr);
    return (l,\<gamma>,\<mu>[i := None])
  }"

(*
  The return here is a pair (val \<times> state) option. The state is necessary because malloc and free
  are expressions and those modify the state. We treat this as an option because None would be
  a special error state in which the evaluation got stuck i.e. sum of two pointers.
*)

text \<open>About variable scoping: When writing to or reading a variable and there's different
  variables with the same name in different scope, or the variable we want to modify is in a
  more general scope we must know in which order these scopes are traversed.
  We can face different situations:

  * Two variables with the same name in different scopes:
      We will always be selected the variable in the local procedure scope over the global
      variable.
  * The variable is in the local scope:
      We select the variable in the local scope.
  * The variable is in the global scope:
      We will check the local scope for the variable, when it's not found then we proceed to
      check the global scope and select the correct variable.\<close>

text \<open>Reads a variable from a state. This works at the level of the visible state because it
  doesn't temper with the stack but only needs the valuation for the local variables.
  First the local variables will be checked for the variable we try to read, we return it's value
  if it's found. If the variable we try to read is not in the locals then we check the globals,
  we return the value of the global, if it exists, otherwise we return None.\<close>
definition read_var :: "vname \<Rightarrow> visible_state \<hookrightarrow> val" where
  "read_var \<equiv> \<lambda>x (l,\<gamma>,\<mu>). do {
    case l x of
      Some (Some v) \<Rightarrow> return v
    | Some None \<Rightarrow> uninitalized_error  
    | None \<Rightarrow> do {
        case \<gamma> x of
          Some (Some v) \<Rightarrow> return v
        | Some None \<Rightarrow> uninitalized_error  
        | None \<Rightarrow> type_error  (* Non-existing variable counts as type error here *)
      } 
  }"

text \<open>Writes a variable in a state. This works at the level of the visible state because it
  doesn't temper with the stack but only needs the valuation for the local variables.
  First the local variables will be checked for the variable we try to write to, we update the
  value of it if it's found. If the variable we try to write to is not in the locals then we
  check the globals, we update the value of the global variable, if it exists, otherwise
  we return None. In the case where the write was successful we return the visible state with
  the updated variable.\<close>
definition write_var :: "vname \<Rightarrow> val \<Rightarrow> visible_state \<hookrightarrow> visible_state" where
  "write_var \<equiv> \<lambda>x v (l,\<gamma>,\<mu>). do {
    case l x of
      Some _ \<Rightarrow> do {
        let l = l (x \<mapsto> Some v);
        return (l,\<gamma>,\<mu>)
      }
    | None \<Rightarrow> do {
        assert (\<gamma> x \<noteq> None) (EStatic EType); (* Access to non-existing variable counts as type-error here *)
        let \<gamma> = \<gamma>(x \<mapsto> Some v);
        return (l,\<gamma>,\<mu>)
      }
  }"

subsection \<open>Evaluation function\<close>

text \<open>We define an evaluation function for @{term exp} and @{term lexp}. It works at the
  @{term visible_state} level, since the evaluation of expressions will not temper with the
  stack and it's only dependent on the locals valuation of the current @{term stack_frame}.

  In the case for @{term "Const c"} and @{term Null} expressions we return the constant values
  @{term "I c"} and @{term NullVal} respectively without modifying the state.

  For a @{term "V x"} we use the @{term read_var} definition and return the read value.

  For expressions that consist of two operands (@{term Plus}, @{term Subst}, @{term Div},
  @{term Mod}, @{term Mult}, @{term Less}, @{term And}, @{term Or}, @{term Eq}) we call
  recursively the evaluate function and then use the correspondent auxiliary evaluation
  function on the values yielded by the recursive call and return the value obtained from it.

  For expressions @{term Minus} and @{term Not} that consist of one operand we call recursively
  the evaluate function and then use the correspondent auxiliary evaluation function on the
  values yieled by the recursive call and return the value obtained from it.

  For the @{term New} the expression is evaluated with a recursive call of @{term eval} and
  then the auxiliary function that allocates a new block is called and we return the value
  obtained from it.

  The interesting cases come with pointer evaluation, the evaluation of pointer expressions will
  depend on whether the pointer expression is on the right-hand-side or the left-hand-side.

  Right-hand-side evaluation of expressions:

  A @{term Deref} expression will be evaluated by doing a recursive call on its operand
  and if this is an address then return the result of calling the load function. If not, this
  is an error and None is returned.

  A @{term Ref} will be evaluated by a call of @{term eval_l} with the operator as argument.
  If this call returns an address we return this and the visible state, if it returns None, we
  return None.

  An @{term "Index e\<^sub>1 e\<^sub>2"} will be evaluated by doing a recursive call with both operands as
  arguments and if it returns an address and an integer value then we attempt to load the
  value in that memory location and return that and the state, if what is returned is different
  from an address and an integer then None is returned.

  Left-hand-side evaluation of l-expressions:

  A @{term Derefl} l-expression will be evaluated by doing a call of @{term eval} on its
  operand, if the value returned is an address, we return that address and the state.

  An @{term "Indexl e\<^sub>1 e\<^sub>2"} will be evaluated by doing a call of @{term eval} with both operands
  as arguments and if it returns an address and an integer value then we return the address
  with its offset field updated by adding the integer to it and the state, if what is returned
  is different from an address and an integer then None is returned.
\<close>

fun eval :: "exp \<Rightarrow> visible_state \<hookrightarrow> (val \<times> visible_state)"
and eval_l :: "lexp \<Rightarrow> visible_state \<hookrightarrow> (addr \<times> visible_state)" where
  "eval (Const c) s = do {
    c \<leftarrow> detect_overflow c;
    return (c, s)
  }  "
| "eval Null s = return (NullVal, s)"
| "eval (V x) s = do {
    v \<leftarrow> read_var x s;
    return (v, s)
    }"
| "eval (Plus i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, (l,\<gamma>,\<mu>)) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> plus_val \<mu> v\<^sub>1 v\<^sub>2;
  return (v, (l,\<gamma>,\<mu>))
}"
| "eval (Subst i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, (l,\<gamma>,\<mu>)) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> subst_val \<mu> v\<^sub>1 v\<^sub>2;
  return (v, (l,\<gamma>,\<mu>))
}"
| "eval (Minus i) s = do {
  (v, s) \<leftarrow> eval i s;
  v \<leftarrow> minus_val v;
  return (v, s)
}"
| "eval (Div i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> div_val v\<^sub>1 v\<^sub>2;
  return (v, s)
}"
| "eval (Mod i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> mod_val v\<^sub>1 v\<^sub>2;
  return (v, s)
}"
| "eval (Mult i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> mult_val v\<^sub>1 v\<^sub>2;
  return (v, s)
}"
| "eval (Less i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, (l,\<gamma>,\<mu>)) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> less_val \<mu> v\<^sub>1 v\<^sub>2;
  return (v, (l,\<gamma>,\<mu>))
}"
| "eval (Not b) s = do {
  (v, s) \<leftarrow> eval b s;
  v \<leftarrow> not_val v;
  return (v, s)
}"
| "eval (And b\<^sub>1 b\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval b\<^sub>1 s;
  b\<^sub>1 \<leftarrow> to_bool v\<^sub>1;
  if b\<^sub>1 then do {
    (v\<^sub>2, s) \<leftarrow> eval b\<^sub>2 s;
    b\<^sub>2 \<leftarrow> to_bool v\<^sub>2;
    if b\<^sub>2 then return (true_val,s) else return (false_val,s)
  } else do {
    return (false_val,s)
  }
}"
| "eval (Or b\<^sub>1 b\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval b\<^sub>1 s;
  b\<^sub>1 \<leftarrow> to_bool v\<^sub>1;
  if b\<^sub>1 then return (true_val,s)
  else do {
    (v\<^sub>2, s) \<leftarrow> eval b\<^sub>2 s;
    b\<^sub>2 \<leftarrow> to_bool v\<^sub>2;
    if b\<^sub>2 then return (true_val,s) else return (false_val,s)
  }  
}"
| "eval (Eq e\<^sub>1 e\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval e\<^sub>1 s;
  (v\<^sub>2, (l,\<gamma>,\<mu>)) \<leftarrow> eval e\<^sub>2 s;
  v \<leftarrow> eq_val \<mu> v\<^sub>1 v\<^sub>2;
  return (v, (l,\<gamma>,\<mu>))
}"
| "eval (New _ e) s = do {
  (v, (l, \<gamma>, \<mu>)) \<leftarrow> eval e s;
  (v, \<mu>) \<leftarrow> new_block v \<mu>;
  return (v, (l, \<gamma>, \<mu>))
}"
| "eval (Deref e) s = do {
  (v, (l, \<gamma>, \<mu>)) \<leftarrow> eval e s;
  case v of
    (A addr) \<Rightarrow> do {
      v \<leftarrow> load addr \<mu>;
      return (v, (l, \<gamma>, \<mu>))
    }
  | NullVal \<Rightarrow> pointer_error  
  | _ \<Rightarrow> type_error
}"
| "eval (Ref e) s = do {
  (addr, s) \<leftarrow> eval_l e s;
  return (A addr,s)
}"
| "eval (Index e\<^sub>1 e\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval e\<^sub>1 s;
  (v\<^sub>2, (l, \<gamma>, \<mu>)) \<leftarrow> eval e\<^sub>2 s;
  case (v\<^sub>1, v\<^sub>2) of
    (A addr, I incr) \<Rightarrow> do {
      addr \<leftarrow> ofs_addr \<mu> addr incr;
      v \<leftarrow> load addr \<mu>;
      return (v, (l, \<gamma>, \<mu>))
    }
  | (NullVal, I _) \<Rightarrow> pointer_error  
  | _ \<Rightarrow> type_error
}"
| "eval_l (Derefl e) s = do {
    (v,s) \<leftarrow> eval e s;
    case v of 
      A addr \<Rightarrow> return (addr,s)
    | NullVal \<Rightarrow> pointer_error  
    | _ \<Rightarrow> type_error
  }"
| "eval_l (Indexl e\<^sub>1 e\<^sub>2) s = do {
    (v\<^sub>1,s) \<leftarrow> eval e\<^sub>1 s;
    (v\<^sub>2,s) \<leftarrow> eval e\<^sub>2 s;
    case (v\<^sub>1,v\<^sub>2) of
      (A (base,ofs), I incr) \<Rightarrow> return ((base,ofs+sint incr),s)
    | (NullVal, I _) \<Rightarrow> pointer_error  
    | _ \<Rightarrow> type_error
  }"


export_code eval checking SML

end

