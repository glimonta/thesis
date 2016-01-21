theory Chloe_Monad
imports Error_Monad
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
(*datatype wf_error -- \<open>Static checkers\<close>
  =
    ETypeChecker    -- \<open>Type checker\<close>
(*  | EWf             -- \<open>Well-formedness checks\<close> subsumed by typechecker*)
*)

datatype chloe_error = 
  is_EStatic: EStatic static_error 
| is_EDynamic: EDynamic dynamic_error 
(*| is_EChecker: EChecker wf_error*)

abbreviation "type_error \<equiv> (EStatic EType)"
abbreviation "overflow_error \<equiv> (EDynamic EOverflow)"
abbreviation "div_zero_error \<equiv> (EDynamic EDivZero)"
abbreviation "pointer_error \<equiv> (EDynamic EPtr)"
abbreviation "uninitalized_error \<equiv> (EDynamic EUninitialized)"
abbreviation "structural_error \<equiv> (EStatic EStructure)"

type_synonym ('a) ce = "('a,chloe_error) error"
type_synonym ('a,'b) cefun = "'a \<Rightarrow> 'b ce"

type_notation cefun (infixr "\<hookrightarrow>" 0)

abbreviation "nd_spec P \<equiv> e_spec P is_EDynamic False"

end
