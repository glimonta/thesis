theory Wrong_Scope
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition f_decl :: fun_decl
  where "f_decl \<equiv>
    \<lparr> fun_decl.name = ''f'',
      fun_decl.params = [],
      fun_decl.locals = [xx],
      fun_decl.body =
        xx ::= (Const 42)
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        Callfunv ''f'' [];;
        xx ::= (Const 21) (* Variable xx is only in f's local scope *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''wrong_scope'',
      program.globals = [],
      program.procs = [f_decl, main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "wrong_scope_exec \<equiv> execute_show [] p"

definition "wrong_scope_ex \<equiv> (
  shows_prog p ''''
)"

definition "wrong_scope_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code wrong_scope_ex} @{code wrong_scope_exec} "../TestC" "wrong_scope"\<close>

end