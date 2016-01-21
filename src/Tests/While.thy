theory While
imports Test_Setup
begin

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $ii := Const 0;;

        (* This while loop is executed a definite number of times *)
        WHILE (Less (V ii) (Const 6)) DO
          $ii := (Plus (V ii) (Const 1))
        ;;
  
        (* This while loop is not executed at all *)
        WHILE (Eq (V ii) (Const 0)) DO
          $ii := Const 42
       \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''while'',
      program.structs = [],
      program.globals = ints [ii],
      program.functs = [main_decl n]
    \<rparr>"

definition "while_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code while_export}"../TestC" "while"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "while_test"\<close>

end
