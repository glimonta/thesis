section \<open>Expressions\<close>
theory Exp
imports 
  Main 
  Type
begin

type_synonym vname = string -- \<open>Name of variables\<close>

subsection \<open>Nullary Operators\<close>
datatype op0 = 
  Const int -- \<open>Integer constant\<close>
| Null      -- \<open>The null address, this separates the value 0 from the address null\<close>
| Var vname -- \<open>Variable\<close>
hide_const (open) Const Null Var

subsection \<open>Unary Operators\<close>
datatype op1 = 
  UMinus      -- \<open>Unary minus @{text "-e"}\<close>
| Not         -- \<open>Boolean not @{text "!e"}\<close>
| BNot        -- \<open>Bitwise not @{text "~e"}\<close>
| Deref       -- \<open>Pointer dereference @{text "*e"}\<close>
| Ref         -- \<open>Reference @{text "&e"}\<close>
| Memb mname  -- \<open>Structure Member @{text "e.name"}\<close>
| Membp mname -- \<open>Structure Member @{text "e->name"}\<close>
hide_const (open) UMinus Not BNot Deref Ref
  
subsection \<open>Binary Operators\<close>
datatype op2 =
  Plus | Minus      -- \<open>Additive operations @{text "+,-"}\<close>
| Mult | Div | Mod  -- \<open>Multiplicative operations @{text "*,/,%"}\<close>
| Less | Leq | Eq   -- \<open>Comparison @{text "<,<=,=="}\<close>
| And | Or          -- \<open>Boolean operations @{text "&&,||"}\<close>
| BAnd | BOr | BXor -- \<open>Bitwise operations @{text "&,|,^"}\<close>
| Index             -- \<open>Array indexing @{text "e[e]"}\<close>
hide_const (open) Plus Minus  Mult Div Mod  Less Leq Eq  And Or  BAnd BOr BXor  Index
  

subsection \<open>Expressions\<close>
datatype exp = E0 op0 | E1 op1 exp | E2 op2 exp exp
hide_const (open) E0 E1 E2


subsection \<open>Abbreviations\<close>
locale exp_syntax begin

  no_notation plus (infixl "+" 65)
  no_notation minus (infixl "-" 65)
  no_notation uminus ("- _" [81] 80)
  no_notation times  (infixl "*" 70)
  no_notation nth (infixl "!" 100)
  no_notation HOL.Not ("~ _" [40] 40)

  no_notation HOL.conj (infixr "&" 35)
  no_notation HOL.disj (infixr "|" 30)

  no_notation Pure.eq (infix "==" 2)

  no_notation
    less_eq  ("op <=") and
    less_eq  ("(_/ <= _)" [51, 51] 50) and
    less  ("op <") and
    less  ("(_/ < _)"  [51, 51] 50)

  no_notation power (infixr "^" 80)  

  no_notation inverse_divide (infixl "'/" 70)

  text \<open>Primary\<close>
  abbreviation V where "V x \<equiv> exp.E0 (op0.Var x)"
  abbreviation C where "C x \<equiv> exp.E0 (op0.Const x)"
  abbreviation Null where "Null \<equiv> exp.E0 (op0.Null)"

  notation V ("$")

  text \<open>Postfix\<close>
  abbreviation Index ("_ [_]" [191,191] 190) where "Index \<equiv> exp.E2 op2.Index"
  abbreviation Memb (infixl "." 190) where "Memb e name \<equiv> exp.E1 (op1.Memb name) e"
  abbreviation Membp (infixl "->" 190) where "Membp e name \<equiv> exp.E1 (op1.Membp name) e"
  notation Membp (infixl "\<rightarrow>" 190)

  term "(V x)[b]"
  term "(V x).''name''"
  term "(V x)->''name''"

  text \<open>Unary\<close>
  abbreviation UMinus ("- _" [181] 180) where "UMinus \<equiv> exp.E1 op1.UMinus"
  abbreviation Not ("! _" [181] 180) where "Not \<equiv> exp.E1 op1.Not"
  abbreviation BNot ("~ _" [181] 180) where "BNot \<equiv> exp.E1 op1.BNot"
  abbreviation Deref ("* _" [181] 180) where "Deref \<equiv> exp.E1 op1.Deref"
  abbreviation Ref ("& _" [181] 180) where "Ref \<equiv> exp.E1 op1.Ref"

  text \<open>Multiplicative\<close>
  abbreviation Mult (infixl "*" 170) where "Mult \<equiv> exp.E2 op2.Mult"
  abbreviation Div (infixl "'/" 170) where "Div \<equiv> exp.E2 op2.Div"
  abbreviation Mod (infixl "%" 170) where "Mod \<equiv> exp.E2 op2.Mod"

  term "a*b"
  term "a/b"
  term "a%b"

  text \<open>Additive\<close>
  abbreviation Plus (infixl "+" 160) where "Plus \<equiv> exp.E2 op2.Plus"
  abbreviation Minus (infixl "-" 160) where "Minus \<equiv> exp.E2 op2.Minus"
  term "a+b"
  term "a-b"

  text \<open>Bitwise shift (not yet implemented)\<close>

  text \<open>Relational\<close>
  abbreviation Less (infixl "<" 140) where "Less \<equiv> exp.E2 op2.Less"
  abbreviation Leq (infixl "<=" 140) where "Leq \<equiv> exp.E2 op2.Leq"
  term "a<b"
  term "a<=b"

  text \<open>Equality\<close>
  abbreviation Eq (infixl "==" 130) where "Eq \<equiv> exp.E2 op2.Eq"

  text \<open>Bitwise\<close>
  abbreviation BAnd (infixl "&" 120) where "BAnd \<equiv> exp.E2 op2.BAnd"
  abbreviation BOr (infixl "|" 120) where "BOr \<equiv> exp.E2 op2.BOr"
  abbreviation BXor (infixl "^" 120) where "BXor \<equiv> exp.E2 op2.BXor"

  text \<open>Logical\<close>
  abbreviation And (infixl "&&" 110) where "And \<equiv> exp.E2 op2.And"
  abbreviation Or (infixl "||" 110) where "Or \<equiv> exp.E2 op2.Or"
end


end
