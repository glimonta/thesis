theory Reserved_Keywords_Union
imports "../Tests/Test_Setup"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        ''union'' ::= (Const 42) (* ''union'' is a reserved keyword *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''reserved_keywords_union'',
      program.structs = [], program.globals = ints [''union''],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
