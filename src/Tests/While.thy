theory While
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        ii ::= Const 0;;

        (* This while loop is executed a definite number of times *)
        WHILE (Less (V ii) (Const 6)) DO
          ii ::= (Plus (V ii) (Const 1))
        ;;
  
        (* This while loop is not executed at all *)
        WHILE (Eq (V ii) (Const 0)) DO
          ii ::= Const INT_MAX
       \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''while'',
      program.globals = [ii],
      program.procs = [main_decl]
    \<rparr>"

definition "while_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code while_export}"../TestC" "while"\<close>

end