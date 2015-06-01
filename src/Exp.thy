theory Exp
imports 
  Main 
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Word/Word"
begin

(* Variable names are strings *)
type_synonym vname = string
(* Addresses are a pair of integers (block_id, offset) *)
type_synonym addr = "nat \<times> int"
type_synonym int_width = 32
type_synonym int_val = "int_width word"

(* Null is to separate addresses from values *)
datatype exp = Const int_val
             | Null
             | V     vname
             | Plus  exp exp
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
