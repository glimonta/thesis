theory New
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* New operation doesn't fail unless asking for space of zero or negative size *)
        aa ::= (New (Const 2));; (* New operation of length 2 *)
        bb ::= (New (Const 42)) (* New operation of length 42 *)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''new'',
      program.globals = [aa,bb],
      program.procs = [main_decl]
    \<rparr>"

definition "new_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code new_export}"../TestC" "new"\<close>

end
