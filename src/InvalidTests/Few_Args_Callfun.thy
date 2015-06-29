theory Few_Args_Callfun
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition sum_decl :: fun_decl
  where "sum_decl \<equiv>
    \<lparr> fun_decl.name = ''sum'',
      fun_decl.params = [foo, bar],
      fun_decl.locals = [],
      fun_decl.body = 
        Return (Plus (V foo) (V bar))
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        Callfun baz ''sum'' [Const 21]
        (* Error: Too few arguments for function call *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''few_args_callfun'',
      program.globals = [baz],
      program.procs = [sum_decl, main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "few_args_callfun_exec \<equiv> execute_show [] p"

definition "few_args_callfun_ex \<equiv> (
  shows_prog p ''''
)"

definition "few_args_callfun_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code few_args_callfun_ex} @{code few_args_callfun_exec} "../TestC" "few_args_callfun"\<close>


end
