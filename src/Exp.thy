theory Exp
imports Main
begin

(* Variable names are strings *)
type_synonym vname = string
(* Addresses are integers *)
type_synonym addr = int
(* A value can be either an integer or an address *)
datatype val = I int | A addr
(*
  A state is a pair in which the first element represents the content of the local variables
  and the second element represents the content of the blocked memory.
  The memory is organized in blocks and it is accesed with the address of the block and the index
  of the block we want to access.
  state = (\<sigma>, \<mu>) \<sigma>: content of local variables, \<mu>: content of memory
*)
type_synonym loc = "vname \<Rightarrow> val"
type_synonym mem = "addr \<Rightarrow> int \<Rightarrow> val"
type_synonym state = "loc \<times> mem"

datatype exp = Const val
(*             | Null  In my notes I've got null as an expr I don't get why now *)
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

datatype lexp = Deref exp
              | Index exp exp

fun plus_val :: "val \<Rightarrow> val \<Rightarrow> val" where
  "plus_val (I i\<^sub>1) (I i\<^sub>2) = I (i\<^sub>1 + i\<^sub>2)"
| "plus_val (A a\<^sub>1) (A a\<^sub>2) = A (a\<^sub>1 + a\<^sub>2)"

fun neg_val :: "val \<Rightarrow> val" where
  "neg_val (I i) = (if i = 0 then (I 1) else (I 0))"

fun and_val :: "val \<Rightarrow> val" where
  "neg_val (I i) = (if i = 0 then (I 1) else (I 0))"

(*
  Today when discussed with Prof. Lammich he suggested this retuned a pair (val, state)
  right now I can't remember why that was and it seems unnecesary so I'll remove it
*)
fun eval :: "exp \<Rightarrow> state \<Rightarrow> val" where
  "eval (Const c) s = c"
| "eval (V x) (\<sigma>, \<mu>) = \<sigma> x"
| "eval (Plus v\<^sub>1 v\<^sub>2) s =  (eval v\<^sub>1 s) + (eval v\<^sub>2 s)"
| "eval (Not b) s = neg_val (eval b s)"
| "eval (And b\<^sub>1 b\<^sub>2) s = and_val (eval b\<^sub>1 s) (eval b\<^sub>2 s)"

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
