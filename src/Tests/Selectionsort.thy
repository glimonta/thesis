theory Selectionsort
imports Test_Setup
begin

(* Selectionsort: Takes an array a and its length n and returns the sorted array *)
definition selection_decl :: fun_decl
  where "selection_decl \<equiv> 
    \<lparr> fun_decl.name = ''selection'',
      fun_decl.rtype = None,
      fun_decl.params = [(aa, ty.Ptr ty.I), (nn,ty.I)],
      fun_decl.locals = ints [ii, mm, tt, jj],
      fun_decl.body = 
        FOR ii FROM (Const ( 0)) TO ((V nn) - (Const (1))) DO
          ($mm := (Index (V aa) (V ii));; (* Min *)
          $tt := (V ii);; (* Min index *)
          (FOR jj FROM (Plus (V ii) (Const ( 1))) TO (V nn) DO
            (IF (Less (Index (V aa) (V jj)) (V mm)) THEN
              $mm := (Index (V aa) (V jj));;
              $tt := (V jj)
            ELSE SKIP));;
          (Indexl (V aa) (V tt)) := (Index (V aa) (V ii));;
          (Indexl (V aa) (V ii)) := (V mm))
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv> 
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $aa := malloc ty.I [Const ( 10)];;
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
        ''selection''!([(V aa), (V nn)])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''selection'',
      program.structs = [],
      program.globals = [(aa,ty.Ptr ty.I), (nn,ty.I)],
      program.functs = [selection_decl, main_decl n]
    \<rparr>"

definition "selection_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code selection_export}"../TestC" "selection"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "selection_test"\<close>

end
