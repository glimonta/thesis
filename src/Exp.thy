theory Exp
imports 
  Main 
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Word/Word"
begin

section \<open>Expressions\<close>

subsection \<open>Type definitions \<close>

text \<open>Variable names are strings, Addresses are a pair conformed by a natural number and an integer
  these represent the (block_id, offset). We only work with one integer type, we use the
  @{term word} type of width 64, because we are using a 64 bit architecture to execute our programs.
  the width of the word can be changed by changing @{term int_width}. The words used here are
  interpreted as signed integers\<close>

type_synonym vname = string
type_synonym addr = "nat \<times> int"
type_synonym int_width = 64
type_synonym int_val = "int_width word"

text \<open>We're using signed longs in the translation to C, this are the min, and max values that it's
  possible to represent with signed longs.
  
  Note: We are assuming 2's complement representation here. 
  TODO: The C99-draft requires less numbers to be representable,
    we need to insert a check in the generated program that ensures a 
    compiler implementation compatible with these numbers.
\<close>

abbreviation "int_width \<equiv> len_of TYPE(int_width)"
abbreviation INT_MIN :: int where "INT_MIN \<equiv> - ((2^(int_width - 1)))"
abbreviation INT_MAX :: int where "INT_MAX \<equiv> ((2^(int_width - 1)) - 1)"


subsection \<open>Expressions definition\<close>
text \<open>An expression can be:
  *  @{term "Const i"} to represent an integer constant.
  *  @{term Null} to represent the null address, this separates the value 0 from the address null.
  *  @{term "V x"} to represent a variable.
  *  @{term "Plus i\<^sub>1 i\<^sub>2"} to represent the addition of two expressions.
  *  @{term "Subst i\<^sub>1 i\<^sub>2"} to represent the substraction of two expressions.
  *  @{term "Minus i"} to represent unary minus over an expression.
  *  @{term "Div i\<^sub>1 i\<^sub>2"} to represent the division of two expressions.
  *  @{term "Mod i\<^sub>1 i\<^sub>2"} to represent the modulo operation over two expressions.
  *  @{term "Mult i\<^sub>1 i\<^sub>2"} to represent the multiplication of two expressions.
  *  @{term "Less i\<^sub>1 i\<^sub>2"} to represent the less than operation over two expressions.
  *  @{term "Not b"} to represent the not operation over an expression.
  *  @{term "And b\<^sub>1 b\<^sub>2"} to represent the and operation over two  expressions.
  *  @{term "Or b\<^sub>1 b\<^sub>2"} to represent the or operation over two expressions.
  *  @{term "Eq b\<^sub>1 b\<^sub>2"} to represent the equality operation over two expressions.
  *  @{term "New e"} to represent the allocation of a new memory block of length e.
  *  @{term "Deref e"} to represent the dereferencing operation over an expression (@{term "op *"} in C)
    this expression is used as an rvalue.
  *  @{term "Ref le"} to represent the referencing operation over an expression (@{term "op &"} in C).
  *  @{term "Index a ofs"} to represent the indexing of an array a in the ofs position (@{term "a[ofs]"} in C).
  *  @{term "Derefl e"} to represent the dereferencing operation over an expression (@{term "op *"} in C)
    this expression is used as an lvalue.
  *  @{term "Indexl a ofs"} to represent the indexing of an array a in the ofs position (@{term "a[ofs]"} in C)
    this expression is used as an lvalue.
\<close>

datatype exp = Const int
             | Null
             | V     vname
             | Plus  exp exp
             | Subst exp exp
             | Minus exp
             | Div   exp exp
             | Mod   exp exp
             | Mult  exp exp
             | Less  exp exp
             | Not   exp
             | And   exp exp
             | Or    exp exp
             | Eq    exp exp
             | New   exp
             | Deref exp    (* * *)
             | Ref   lexp    (* & *)
             | Index exp exp (* e[e] *)

and lexp = Derefl exp
         | Indexl exp exp

end
