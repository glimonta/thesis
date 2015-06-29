theory Variable_Returnv
imports "../SmallStep" "../Test" "../Test_Harness"
begin

(* return void in a function with variable return value *)

definition f_decl :: fun_decl
  where "f_decl \<equiv>
    \<lparr> fun_decl.name = ''f'',
      fun_decl.params = [],
      fun_decl.locals = [foo],
      fun_decl.body = 
        foo ::= Const 42;;
        Returnv
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        Callfun bar ''f'' []
        (* Error: The function doesn't return a value to the variable *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''variable_returnv'',
      program.globals = [bar],
      program.procs = [f_decl, main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "variable_returnv_exec \<equiv> execute_show [] p"

definition "variable_returnv_ex \<equiv> (
  shows_prog p ''''
)"

definition "variable_returnv_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code variable_returnv_ex} @{code variable_returnv_exec} "../TestC" "variable_returnv"\<close>


end
