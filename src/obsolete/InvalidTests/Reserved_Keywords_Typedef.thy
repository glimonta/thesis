theory Reserved_Keywords_Typedef
imports "../Tests/Test_Setup"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body =
        ''typedef'' ::= (Const 42) (* ''typedef'' is a reserved keyword *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''reserved_keywords_typedef'',
      program.structs = [], program.globals = ints [''typedef''],
      program.functs = [main_decl]
    \<rparr>"


definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
