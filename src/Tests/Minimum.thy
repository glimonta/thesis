theory Minimum
imports Test_Setup
begin

(* Min: Takes an array a and its length n and returns the minimum element of the array *)
definition min_decl :: fun_decl
  where "min_decl \<equiv>
    \<lparr> fun_decl.name = ''min'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = [(aa, ty.Ptr ty.I), (nn,ty.I)],
      fun_decl.locals = ints [ii, mm],
      fun_decl.body = 
        $mm := (Index (V aa) (Const 0));;
        FOR ii FROM (Const ( 0)) TO (Plus (V nn) (- Const (1))) DO
          (IF (Less (Index (V aa) (V ii)) (V mm))
            THEN $mm := (Index (V aa) (V ii))
          ELSE SKIP);;
          return (V mm)
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $aa := malloc ty.I [(Const ( 10))];;
        (Indexl (V aa) (Const ( 0))) := (Const ( 44));;
        (Indexl (V aa) (Const ( 1))) := (Const ( 98));;
        (Indexl (V aa) (Const ( 2))) := (Const ( 60));;
        (Indexl (V aa) (Const ( 3))) := (Const ( 26));;
        (Indexl (V aa) (Const ( 4))) := (Const ( 54));;
        (Indexl (V aa) (Const ( 5))) := (Const ( 1));;
        (Indexl (V aa) (Const ( 6))) := (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) := (Const ( 84));;
        (Indexl (V aa) (Const ( 8))) := (Const ( 38));;
        (Indexl (V aa) (Const ( 9))) := (Const ( 80));;
        $nn := (Const ( 10));;
        $mm := ''min''!([(V aa), (V nn)])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''min'',
      program.structs = [],
      program.globals = [(aa,ty.Ptr ty.I)]@ ints [nn, mm],
      program.functs = [min_decl, main_decl n]
    \<rparr>"

definition "minimum_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code minimum_export}"../TestC" "min"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "min_test"\<close>


end
