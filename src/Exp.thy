theory Exp
imports Main
begin

(* Variable names are strings *)
type_synonym vname = string
(* Addresses are a pair of integers (block_id, offset) *)
type_synonym addr = "int \<times> int"
(* A value can be either an integer or an address *)
datatype val = I int | A addr
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

(* lists will be accessed by 1 in the first position because A (0,0) is null addr *)
fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 1 then x else xs !! (i - 1))"

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
             | Free  exp
             | Deref exp     (* * *)
             | Ref   exp     (* & *)
             | Index exp exp (* e[e] *)

datatype lexp = Derefl exp
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

(* Returns a new block of memory of size v, initialized with 0s *)
fun init_block :: "nat \<Rightarrow> val list" where
  "init_block 0 = []"
| "init_block (Suc i) = (I 0) # init_block i"

(* Allocates a new block in the memory *)
(* 
  This is using conversions between int and nat I don't know what happens if the number in 
  (I i) is neg
*)
fun new_block :: "val \<Rightarrow> mem \<Rightarrow> mem option" where
  "new_block (I i) \<mu> = (if i < list_size \<mu> then None else Some (\<mu> @ [init_block (nat i)]))"
| "new_block (A a) _ = None"

value "new_block (I 2) [[]]"

(* In indexes 0 nothing should be stored *)
fun get_mem :: "val \<Rightarrow> mem \<Rightarrow> val option" where
  "get_mem (I i) _ = None"
| "get_mem (A (i,j)) \<mu> = (if (i=0 \<or> j=0) then None else Some ((\<mu> !! i) !! j))"

value "get_mem (A (0,0)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"
value "get_mem (A (1,2)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"
value "get_mem (A (2,3)) [[(I 1), (I 2)], [(I 3), (I 4), (I 5)]]"

fun index_mem :: "val \<Rightarrow> val \<Rightarrow> mem \<Rightarrow> val option" where
  "index_mem (A (x,y)) (I i) \<mu> = get_mem (A (x, (y + i))) \<mu>"
| "index_mem _ _ _ = None"

(*
  The return here is a pair (val \<times> state) option. The state is necessary because malloc and free
  are expressions and those modify the state. We treate this as an option because None would be
  a special error state in which the evaluation got stuck i.e. sum of two pointers.
*)
fun eval :: "exp \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "eval (Const c) s = Some (c, s)"
| "eval Null s = Some (A (0,0), s)"
| "eval (V x) (\<sigma>, \<mu>) = Some (\<sigma> x, (\<sigma>, \<mu>))"
| "eval (Plus i\<^sub>1 i\<^sub>2) s =  (case (eval i\<^sub>1 s) of
                            None \<Rightarrow> None |
                            Some (v\<^sub>1, s') \<Rightarrow> (case (eval i\<^sub>2 s') of
                                               None \<Rightarrow> None |
                                               Some (v\<^sub>2, s'') \<Rightarrow> (case (plus_val v\<^sub>1 v\<^sub>2) of
                                                                   None \<Rightarrow> None |
                                                                   Some v \<Rightarrow> Some (v, s''))))"
| "eval (Less i\<^sub>1 i\<^sub>2) s = (case (eval i\<^sub>1 s) of
                           None \<Rightarrow> None |
                           Some (v\<^sub>1, s') \<Rightarrow> (case (eval i\<^sub>2 s') of
                                              None \<Rightarrow> None |
                                              Some (v\<^sub>2, s'') \<Rightarrow> (case (less_val v\<^sub>1 v\<^sub>2) of
                                                                  None \<Rightarrow> None |
                                                                  Some v \<Rightarrow> Some (v, s''))))"
| "eval (Not b) s = (case (eval b s) of 
                       None \<Rightarrow> None |
                       Some (b', s) \<Rightarrow> (case (not_val b') of
                                          None \<Rightarrow> None |
                                          Some b'' \<Rightarrow> Some (b'', s)))"
| "eval (And b\<^sub>1 b\<^sub>2) s = (case (eval b\<^sub>1 s) of
                           None \<Rightarrow> None |
                           Some (v\<^sub>1, s') \<Rightarrow> (case (eval b\<^sub>2 s') of
                                              None \<Rightarrow> None |
                                              Some (v\<^sub>2, s'') \<Rightarrow> (case (and_val v\<^sub>1 v\<^sub>2) of
                                                                  None \<Rightarrow> None |
                                                                  Some v \<Rightarrow> Some (v, s''))))"
| "eval (New e) s = (case (eval e s) of
                       None \<Rightarrow> None |
                       Some (v, (\<sigma>, \<mu>)) \<Rightarrow> (case (new_block v \<mu>) of
                                              None \<Rightarrow> None |
                                              Some \<mu>' \<Rightarrow> Some ((I (list_size \<mu>')), (\<sigma>, \<mu>'))))"
| "eval (Deref e) s = (case (eval e s) of
                         None \<Rightarrow> None |
                         Some (v, (\<sigma>, \<mu>)) \<Rightarrow> (case (get_mem v \<mu>) of
                                                None \<Rightarrow> None |
                                                Some v' \<Rightarrow> Some (v', (\<sigma>,\<mu>))))"
| "eval (Ref e) s = (case (eval e s) of
                       None \<Rightarrow> None |
                       Some (v, s') \<Rightarrow> (case v of
                                          (I _) \<Rightarrow> None |
                                          (A _) \<Rightarrow> Some (v,s')))"
| "eval (Index e\<^sub>1 e\<^sub>2) s = (case (eval e\<^sub>1 s) of
                            None \<Rightarrow> None |
                            Some (v\<^sub>1, s') \<Rightarrow> (case (eval e\<^sub>2 s') of
                                               None \<Rightarrow> None |
                                               Some (v\<^sub>2, (\<sigma>, \<mu>)) \<Rightarrow> (case (index_mem v\<^sub>1 v\<^sub>2 \<mu>) of
                                                                      None \<Rightarrow> None |
                                                                      Some v \<Rightarrow> Some(v, (\<sigma>,\<mu>)))))"

fun eval_l :: "lexp \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "eval_l (Derefl e) s = (case (eval e s) of
                            None \<Rightarrow> None |
                            Some (v, s') \<Rightarrow> (case v of
                                               (I _) \<Rightarrow> None |
                                               (A _) \<Rightarrow> Some (v, s')))"
| "eval_l (Indexl e\<^sub>1 e\<^sub>2) s = (case (eval e\<^sub>1 s) of
                               None \<Rightarrow> None |
                               Some (v\<^sub>1, s') \<Rightarrow> (case (eval e\<^sub>2 s') of
                                                  None \<Rightarrow> None |
                                                  Some (v\<^sub>2, s'') \<Rightarrow> (case (plus_val v\<^sub>1 v\<^sub>2) of
                                                                      None \<Rightarrow> None |
                                                                      Some v \<Rightarrow> Some(v, s''))))"

(*
text_raw{*\snip{AExpaexpdef}{2}{1}{% *}
datatype aexp = N int | V vname | Plus aexp aexp
text_raw{*}%endsnip*}

text_raw{*\snip{AExpavaldef}{1}{2}{% *}
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"
text_raw{*}%endsnip*}


value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text {* The same state more concisely: *}
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

text {* \noindent
  We can now write a series of updates to the function @{text "\<lambda>x. 0"} compactly:
*}
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text {* In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
*}
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text{* Note that this @{text"<\<dots>>"} syntax works for any function space
@{text"\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2"} where @{text "\<tau>\<^sub>2"} has a @{text 0}. *}


subsection "Constant Folding"

text{* Evaluate constant subsexpressions: *}

text_raw{*\snip{AExpasimpconstdef}{0}{2}{% *}
fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)"
text_raw{*}%endsnip*}

theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
apply(induction a)
apply (auto split: aexp.split)
done

text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}

text_raw{*\snip{AExpplusdef}{0}{2}{% *}
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
text_raw{*}%endsnip*}

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

text_raw{*\snip{AExpasimpdef}{2}{0}{% *}
fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"
text_raw{*}%endsnip*}

text{* Note that in @{const asimp_const} the optimized constructor was
inlined. Making it a separate function @{const plus} improves modularity of
the code and the proofs. *}

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a)
apply simp_all
done

end
*)



end
