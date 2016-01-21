theory Eq
imports Test_Setup
begin

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $aa := malloc ty.I [Const 10];;
        $bb := malloc ty.I [Const 10];;
        $cc := (Plus (V aa) (Const 2));;
      (* True, two integers*)
        $dd := (Eq (Const 42) (Const 42));;
      (* False, two integers *)
        $ee := (Eq (Const 0) (Const 23));;
      (* True, two addresses *)
        $ff := (Eq (V aa) (V aa));;
      (* False, two addresses *)
        $gg := (Eq (V aa) (V cc));;
      (* False, two addresses *)
        $hh := (Eq (V aa) (V bb));;
      (* False, two addresses *)
        $ii := (Eq (V cc) (V bb))
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''eq'',
      program.structs = [],
      program.globals = int_ptrs [aa,bb,cc] @ ints [dd,ee,ff,gg,hh,ii],
      program.functs = [main_decl n]
    \<rparr>"

definition "eq_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code eq_export}"../TestC" "eq"\<close>

end
