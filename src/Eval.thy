theory Eval
imports Com Exp
begin

(* A value can be either an integer or an address *)
datatype val = NullVal | I int_val | A addr

(*
  A state is a pair in which the first element represents the content of the local variables
  and the second element represents the content of the blocked memory.
  The memory is organized in blocks and it is accesed with the address of the block and the index
  of the block we want to access. The memory is encoded as a list of blocks, and each block is
  a list of values.
  state = (\<sigma>, \<mu>) \<sigma>: content of local variables, \<mu>: content of memory
*)

datatype return_loc = Ar addr | Vr vname
(* A valuation is a function that maps variable names to values, name of variable where to save the
   return value of the function, address where to save the return value of the function *)
type_synonym valuation = "vname \<Rightarrow> val option option"
type_synonym mem = "val option list option list"

type_synonym stack_frame = "com \<times> valuation \<times> return_loc"

(* Stack, globals, procedure table, memory *)
type_synonym state = "stack_frame list \<times> valuation \<times> mem"

type_synonym visible_state = "valuation \<times> valuation \<times> mem"

definition lift_transformer :: 
  "(visible_state \<rightharpoonup> ('a\<times>visible_state))
  \<Rightarrow> state \<rightharpoonup> ('a \<times> state)"
where
  "lift_transformer tr \<equiv> \<lambda>((com,locals,rloc)#\<sigma>,\<gamma>,\<mu>) \<Rightarrow> do {
    (r,(locals,\<gamma>,\<mu>)) \<leftarrow> tr (locals,\<gamma>,\<mu>);
    Some (r,((com,locals,rloc)#\<sigma>,\<gamma>,\<mu>))
  }"



fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

abbreviation "list_size xs \<equiv> int(length xs)"

fun plus_val :: "val \<Rightarrow> val \<Rightarrow> val option" where
  "plus_val (I i\<^sub>1) (I i\<^sub>2) = Some (I (i\<^sub>1 + i\<^sub>2))"
| "plus_val (A (x,y)) (I i) = Some (A (x, y + sint i))"
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

definition store :: "addr \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state option" where
  "store \<equiv> \<lambda>(i,j) v (\<sigma>,\<gamma>,\<mu>).
    if valid_mem (i,j) \<mu> then
      Some (\<sigma>,\<gamma>,\<mu>[i := Some ( the (\<mu>!i) [nat j := Some v] )])
    else
      None"

definition free :: "addr \<Rightarrow> mem \<Rightarrow> mem option" where
  "free \<equiv>  \<lambda>(i,j) \<mu>.
    if valid_mem (i,j) \<mu> then
      Some (\<mu>[i := None])
    else
      None"

(*
fun get_mem :: "val \<Rightarrow> mem \<Rightarrow> val option" where
  "get_mem (A (i,j)) \<mu> = (if valid_mem (i,j) \<mu> then Some ((\<mu> !! i) !! j) else None)"
| "get_mem _ _ = None"

value "get_mem (A (0,0)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"
value "get_mem (A (1,2)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"
value "get_mem (A (2,3)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"

fun index_mem :: "val \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> val option" where
  "index_mem (A (x,y)) (I i) \<mu> = get_mem (A (x, (y + i))) \<mu>"
| "index_mem _ _ _ = None"
*)

(*
  The return here is a pair (val \<times> state) option. The state is necessary because malloc and free
  are expressions and those modify the state. We treat this as an option because None would be
  a special error state in which the evaluation got stuck i.e. sum of two pointers.
*)

definition "assert \<Phi> \<equiv> if \<Phi> then Some () else None"

fun read_var :: "vname \<Rightarrow> state \<Rightarrow> val option" where
  "read_var x (\<sigma>,\<gamma>,\<mu>) = do {
    assert (\<sigma> \<noteq> []);
    let (_,locals,_) = hd \<sigma>;
    case locals x of
      Some v \<Rightarrow> v
    | None \<Rightarrow> do {
        case \<gamma> x of
          Some v \<Rightarrow> v
        | None \<Rightarrow> None  
      } 
  }"

fun write_var :: "vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state option" where
  "write_var x v (\<sigma>,\<gamma>,\<mu>) = do {
    assert (\<sigma> \<noteq> []);
    let (pc,locals,ra) = hd \<sigma>;
    case locals x of
      Some _ \<Rightarrow> do {
        let locals = locals (x \<mapsto> Some v);
        let \<sigma> = (pc,locals, ra)#tl \<sigma>;
        Some (\<sigma>,\<gamma>,\<mu>)
      }
    | None \<Rightarrow> do {
        assert (\<gamma> x \<noteq> None);
        let \<gamma> = \<gamma>(x \<mapsto> Some v);
        Some (\<sigma>,\<gamma>,\<mu>)
      }
  }"


fun eval :: "exp \<Rightarrow> state \<Rightarrow> (val \<times> state) option"
and eval_l :: "lexp \<Rightarrow> state \<Rightarrow> (addr \<times> state) option" where
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
  (v, (\<sigma>, \<gamma>, \<mu>)) \<leftarrow> eval e s;
  (v, \<mu>) \<leftarrow> new_block v \<mu>;
  Some (v, (\<sigma>, \<gamma>, \<mu>))
}"
| "eval (Deref e) s = do {
  (v, (\<sigma>, \<gamma>, \<mu>)) \<leftarrow> eval e s;
  case v of
    (A addr) \<Rightarrow> do {
      v \<leftarrow> load addr \<mu>;
      Some (v, (\<sigma>, \<gamma>, \<mu>))
    }
  | _ \<Rightarrow> None
}"
| "eval (Ref e) s = (case (eval_l e s) of
                       None \<Rightarrow> None |
                       Some (addr, s) \<Rightarrow> Some (A addr,s))"
| "eval (Index e\<^sub>1 e\<^sub>2) s = do {
  (v\<^sub>1, s) \<leftarrow> eval e\<^sub>1 s;
  (v\<^sub>2, (\<sigma>, \<gamma>, \<mu>)) \<leftarrow> eval e\<^sub>2 s;
  case (v\<^sub>1, v\<^sub>2) of
    (A addr, I incr) \<Rightarrow> do {
      v \<leftarrow> load (ofs_addr addr incr) \<mu>;
      Some (v, (\<sigma>, \<gamma>, \<mu>))
    }
  | _ \<Rightarrow> None
}"
| "eval_l (Derefl e) s = do {
    (v,s) \<leftarrow> eval e s;
    case v of A addr \<Rightarrow> Some (addr,s)
    | _ \<Rightarrow> None
  }"
(*| "eval_l (Indexl e\<^sub>1 e\<^sub>2) s = do {
    (v\<^sub>1,s) \<leftarrow> eval e\<^sub>1 s;
    (v\<^sub>2,s) \<leftarrow> eval e\<^sub>2 s;
    v \<leftarrow> plus_val v\<^sub>1 v\<^sub>2;
    case v of
      A addr \<Rightarrow> Some (addr,s)
    | _ \<Rightarrow> None
  }"*)
| "eval_l (Indexl e\<^sub>1 e\<^sub>2) s = do {
    (v\<^sub>1,s) \<leftarrow> eval e\<^sub>1 s;
    (v\<^sub>2,s) \<leftarrow> eval e\<^sub>2 s;
    case (v\<^sub>1,v\<^sub>2) of
      (A (base,ofs), I incr) \<Rightarrow> Some ((base,ofs+sint incr),s)
    | _ \<Rightarrow> None
  }"


(*
(case (eval e s) of
                            None \<Rightarrow> None |
                            Some (v, s') \<Rightarrow> (case v of
                                               (I _) \<Rightarrow> None |
                                               NullVal \<Rightarrow> None |
                                               (A _) \<Rightarrow> Some (v, s')))"
*)
(*
| "eval_l (Indexl e\<^sub>1 e\<^sub>2) s = (case (eval e\<^sub>1 s) of
                                None \<Rightarrow> None |
                                Some (v\<^sub>1, s) \<Rightarrow> (case (eval e\<^sub>2 s) of
                                                  None \<Rightarrow> None |
                                                  Some (v\<^sub>2, s) \<Rightarrow> (case (plus_val v\<^sub>1 v\<^sub>2) of
                                                                    None \<Rightarrow> None |
                                                                    Some v \<Rightarrow> (case v of
                                                                                 (I _) \<Rightarrow> None |
                                                                                 NullVal \<Rightarrow> None |
                                                                                 (A _) \<Rightarrow> Some (v, s)))))"
*)


end

