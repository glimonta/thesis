theory Deref
imports Test_Setup
begin

definition init_decl :: fun_decl
  where "init_decl \<equiv>
    \<lparr> fun_decl.name = ''init'',
      fun_decl.rtype = None,
      fun_decl.params = [(aa,ty.Ptr ty.I), (nn, ty.I)],
      fun_decl.locals = ints [ii],
      fun_decl.body = 
        $ii := Const 0;;
        WHILE (Less (V ii) (V nn)) DO (
          (Indexl (V aa) (V ii)) := (V ii);;
          $ii := (Plus (V ii) (Const 1))
        )
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $nn := Const 10;;
        $aa := malloc (ty.I) [V nn];;

        ''init''!([V aa, V nn]);;

        (* j contains the number of matches with the content in memory *)
        $ii := Const 0;;
        $jj := Const 0;;
        WHILE (Less (V ii) (V nn)) DO (
          (IF (Eq (Deref (Plus (V aa) (V ii))) (V ii)) THEN
            $jj := (Plus (V jj) (Const 1))
          ELSE
            SKIP);;
          $ii := (Plus (V ii) (Const 1))
        )
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''deref'',
      program.structs = [],
      program.globals = (aa,ty.Ptr ty.I)#ints [nn,ii,jj],
      program.functs = [init_decl, main_decl n]
    \<rparr>"

definition "deref_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code deref_export}"../TestC" "deref"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "deref_test"\<close>

end
