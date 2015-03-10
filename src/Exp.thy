theory Exp
imports Main "~~/src/HOL/Library/Monad_Syntax"
begin

(* Variable names are strings *)
type_synonym vname = string
(* Addresses are a pair of integers (block_id, offset) *)
type_synonym addr = "int \<times> int"
(* A value can be either an integer or an address *)
datatype val = NullVal | I int | A addr
(*
  A state is a pair in which the first element represents the content of the local variables
  and the second element represents the content of the blocked memory.
  The memory is organized in blocks and it is accesed with the address of the block and the index
  of the block we want to access. The memory is encoded as a list of blocks, and each block is
  a list of values.
  state = (\<sigma>, \<mu>) \<sigma>: content of local variables, \<mu>: content of memory
*)
type_synonym loc = "vname \<Rightarrow> val"
type_synonym mem = "val list list"
type_synonym state = "loc \<times> mem"

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

abbreviation "list_size xs \<equiv> int(length xs)"

(* Null is to separate addresses from values *)
datatype exp = Const val
             | Null          
             | V     vname
             | Plus  exp exp
             | Less  exp exp
             | Not   exp
             | And   exp exp
             | New   exp
             | Deref exp    (* * *)
             | Ref   lexp    (* & *)
             | Index exp exp (* e[e] *)

and lexp = Derefl exp
         | Indexl exp exp

fun plus_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "plus_val (I i\<^sub>1) (I i\<^sub>2) = Some (I (i\<^sub>1 + i\<^sub>2))"
| "plus_val (A (x,y)) (I i) = Some (A (x, y+i))"
| "plus_val a\<^sub>1 a\<^sub>2 = None"

fun less_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "less_val (I i\<^sub>1) (I i\<^sub>2) = (if i\<^sub>1 < i\<^sub>2 then Some (I 1) else Some (I 0))"
| "less_val a\<^sub>1 a\<^sub>2 = None"


fun not_val :: "val \<Rightarrow> val option" where
  "not_val (I i) = (if i = 0 then Some (I 1) else Some (I 0))"
| "not_val a = None"

fun and_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "and_val (I i\<^sub>1) (I i\<^sub>2) = (if i\<^sub>1 = 0 then Some (I 0) else (if i\<^sub>2 = 0 then Some (I 0) else Some (I 1)))"
| "and_val a\<^sub>1 a\<^sub>2 = None"

(* Allocates a new block in the memory *)
(* n
  This is using conversions between int and nat I don't know what happens if the number in 
  (I i) is neg
*)
fun new_block :: "val \<Rightarrow> mem \<Rightarrow> (val \<times> mem) option" where
  "new_block (I i) \<mu> = Some ((A (list_size \<mu>, 0)), \<mu> @ [replicate (nat i) (I 0)])"
| "new_block _ _ = None"

value "new_block (I 2) [[]]"

(* In indexes 0 nothing should be stored *)
fun get_mem :: "val \<Rightarrow> mem \<Rightarrow> val option" where
  "get_mem (A (i,j)) \<mu> = (if (i=0 \<or> j=0) then None else Some ((\<mu> !! i) !! j))"  
| "get_mem _ _ = None"

value "get_mem (A (0,0)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"
value "get_mem (A (1,2)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"
value "get_mem (A (2,3)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"

fun index_mem :: "val \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> val option" where
  "index_mem (A (x,y)) (I i) \<mu> = get_mem (A (x, (y + i))) \<mu>"
| "index_mem _ _ _ = None"

(*
  The return here is a pair (val \<times> state) option. The state is necessary because malloc and free
  are expressions and those modify the state. We treat this as an option because None would be
  a special error state in which the evaluation got stuck i.e. sum of two pointers.
*)
fun eval :: "exp \<Rightarrow> state \<Rightarrow> (val \<times> state) option"
and eval_l :: "lexp \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "eval (Const c) s = Some (c, s)"
| "eval Null s = Some (NullVal, s)"
| "eval (V x) (\<sigma>, \<mu>) = Some (\<sigma> x, (\<sigma>, \<mu>))"
| "eval (Plus i\<^sub>1 i\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval i\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval i\<^sub>2 s;
  v \<leftarrow> plus_val v\<^sub>1 v\<^sub>2;
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
| "eval (New e) s = do {
  (v, (\<sigma>, \<mu>)) \<leftarrow> eval e s;
  (v, \<mu>) \<leftarrow> new_block v \<mu>;
  Some (v, (\<sigma>, \<mu>))
}"
| "eval (Deref e) s = do {
  (v, (\<sigma>, \<mu>)) \<leftarrow> eval e s;
  v \<leftarrow> get_mem v \<mu>;
  Some (v, (\<sigma>, \<mu>))
}"
| "eval (Ref e) s = (case (eval_l e s) of
                       None \<Rightarrow> None |
                       Some (v, s') \<Rightarrow> (case v of
                                          (I _) \<Rightarrow> None |
                                          (A _) \<Rightarrow> Some (v,s')))"
| "eval (Index e\<^sub>1 e\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval e\<^sub>1 s;
  (v\<^sub>2, (\<sigma>, \<mu>)) \<leftarrow> eval e\<^sub>2 s;
  v \<leftarrow> index_mem v\<^sub>1 v\<^sub>2 \<mu>;
  Some (v, (\<sigma>, \<mu>))
}"
| "eval_l (Derefl e) s = (case (eval e s) of
                            None \<Rightarrow> None |
                            Some (v, s') \<Rightarrow> (case v of
                                               (I _) \<Rightarrow> None |
                                               (A _) \<Rightarrow> Some (v, s')))"
| "eval_l (Indexl e\<^sub>1 e\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval e\<^sub>1 s;
  (v\<^sub>2, s) \<leftarrow> eval e\<^sub>2 s;
  v \<leftarrow> plus_val v\<^sub>1 v\<^sub>2;
  Some (v, s)
}"

end
