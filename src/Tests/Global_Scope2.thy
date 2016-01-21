theory Global_Scope2
imports Test_Setup
begin

definition mult_decl :: fun_decl
  where "mult_decl \<equiv>
    \<lparr> fun_decl.name = ''mult'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = ints [ii, jj],
      fun_decl.locals = [],
      fun_decl.body = 
        (* The foo accessed here is the global one, not the one in double *)
        $foo := Const 42;;
        return (Mult (V ii) (V jj))
    \<rparr>"

definition doub_decl :: fun_decl
  where "doub_decl \<equiv>
    \<lparr> fun_decl.name = ''doub'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = ints [ii],
      fun_decl.locals = ints [foo],
      fun_decl.body = 
        (* The foo accessed here is the local one, not the global one *)  
        $foo := ''mult''!([(V ii), (V ii)]);;
        RETURN (V foo)
    \<rparr>"


definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $foo := Const 21;;
        $bar := ''doub''!([(Const 4)]);;
        IF (Eq (V foo) (Const (42))) THEN
        (* We should be using the global variable in the global context *)
          $baz := Const 1
        ELSE
        (* Otherwise we generate an error in the program *)
          $baz := (Plus (Const INT_MAX) (Const 1))
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''global_scope2'',
      program.structs = [],
      program.globals = ints [foo, bar, baz],
      program.functs = [mult_decl, doub_decl, main_decl n]
    \<rparr>"


definition "global_scope2_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code global_scope2_export}"../TestC" "global_scope2"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "global_scope2_test"\<close>

end
