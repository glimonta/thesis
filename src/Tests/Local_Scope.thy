theory Local_Scope
imports Test_Setup
begin

definition mult_decl :: fun_decl
  where "mult_decl \<equiv>
    \<lparr> fun_decl.name = ''mult'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = ints [ii, jj],
      fun_decl.locals = ints [foo],
      fun_decl.body = 
        (* The foo accessed here is the local one, not the global one *)
        $foo := V ii;;
        RETURN (Mult (V foo) (V jj))
    \<rparr>"                                

definition main_decl 
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        (* The mult function access a variable that's not in it's local scope *)
        $foo := Const 21;;
        $bar := ''mult''!([(Const 2), (Const 4)]);;
        IF (Eq (V foo) (Const 21)) THEN
        (* If the value of global foo wasn't modified then we assign true to baz *)
          $baz := Const 1
        ELSE
        (* Otherwise we generate an error in the program *)
          $baz := (Plus (Const INT_MAX) (Const 1))
    \<rparr>"

definition p 
  where "p n \<equiv> 
    \<lparr> program.name = ''local_scope'',
      program.structs = [],
      program.globals = ints [foo, bar, baz],
      program.functs = [mult_decl, main_decl n]
    \<rparr>"

definition "local_scope_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code local_scope_export}"../TestC" "local_scope"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "local_scope"\<close>

end
