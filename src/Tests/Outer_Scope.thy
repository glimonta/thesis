theory Outer_Scope
imports Test_Setup
begin

definition mult_foo_decl :: fun_decl
  where "mult_foo_decl \<equiv>
    \<lparr> fun_decl.name = ''mult_foo'',
      fun_decl.rtype = None,
      fun_decl.params = ints [ii],
      fun_decl.locals = [],
      fun_decl.body = 
        $foo := Mult (V foo) (V ii)
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
        ''mult_foo''!([(Const 2)]);;
        IF ($foo == C 42) THEN
          $bar := Const 1 (* If it's correct then we set bar to true *)
        ELSE
          $bar := (Plus (Const INT_MAX) (Const 1)) (* Otherwise we generate an error in the program *)
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''outer_scope'',
      program.structs = [],
      program.globals = ints [foo, bar],
      program.functs = [mult_foo_decl, main_decl n]
    \<rparr>"

definition "outer_scope_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code outer_scope_export}"../TestC" "outer_scope"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "outer_scope_test"\<close>


end
