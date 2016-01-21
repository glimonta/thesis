theory New
imports Test_Setup
begin

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* New operation doesn't fail unless asking for space of zero or negative size *)
        $aa := malloc ty.I [(Const 2)];; (* New operation of length 2 *)
        $bb := malloc ty.I [(Const 42)] (* New operation of length 42 *)
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''new'',
      program.structs = [],
      program.globals = int_ptrs [aa,bb],
      program.functs = [main_decl n]
    \<rparr>"

definition "new_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code new_export}"../TestC" "new"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "new_test"\<close>


end
