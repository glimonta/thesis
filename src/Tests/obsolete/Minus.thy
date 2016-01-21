theory Minus
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Minus (Const 2));; (* Minus operation on positive values *)
        bb ::= (Minus (Const (-1))) (* Minus operation on negative values *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''minus'',
      program.globals = [aa,bb],
      program.procs = [main_decl]
    \<rparr>"

definition "minus_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code minus_export}"../TestC" "minus"\<close>

end
