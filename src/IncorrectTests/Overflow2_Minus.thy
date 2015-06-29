theory Overflow2_Minus
imports "../SmallStep" "../Test" "../Test_Harness"
begin

value "INT_MIN -1"
value "shows (word_of_int (INT_MIN - 1)) ''''"
value "shows_exp (Const ((word_of_int INT_MIN))) ''''"
value "(Const ((word_of_int (INT_MIN - 1))))"
value "(Const (word_of_int (-32)))"
value "shows_exp (Const (word_of_int (-32))) ''''"
value "shows_exp (Minus (Const (word_of_int INT_MIN - 1))) ''''"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        xx ::= (Minus (Const ((word_of_int INT_MIN) - 1))) (* Overflow *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''overflow2_minus'',
      program.globals = [xx],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "overflow2_minus_exec \<equiv> execute_show [] p"

definition "overflow2_minus_ex \<equiv> (
  shows_prog p ''''
)"

definition "overflow2_minus_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"

setup \<open>export_c_code @{code overflow2_minus_ex} @{code overflow2_minus_exec} "../TestC" "overflow2_minus"\<close>


end
