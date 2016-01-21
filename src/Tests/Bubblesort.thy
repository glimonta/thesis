theory Bubblesort
imports "Test_Setup"
begin

(* Bubblesort: Takes an array a and its length n and returns the sorted array *)
definition bubblesort_decl :: fun_decl
  where "bubblesort_decl \<equiv>
    \<lparr> fun_decl.name = ''bubblesort'',
      fun_decl.rtype = None,
      fun_decl.params = (aa,ty.Ptr ty.I) # ints([nn]),
      fun_decl.locals = ints [ii,jj, tt],
      fun_decl.body = 
        $tt := C 0;;
        FOR ii FROM (C 1) TO (V nn) DO
          (FOR jj FROM (C ( 0)) TO ($nn - C 1) DO
            (IF (Less (Index (V aa) (Plus (V jj) (C ( 1)))) (Index (V aa) (V jj)))
            THEN ($tt := (Index (V aa) (V jj));;
              (Index (V aa) (V jj)) := (Index (V aa) (Plus (V jj) (C ( 1))));;
              (Index (V aa) (Plus (V jj) (C ( 1)))) := (V tt))
            ELSE SKIP))
    \<rparr>"                                

definition main_decl :: "fname \<Rightarrow> fun_decl"
  where "main_decl mname \<equiv>
    \<lparr> fun_decl.name = mname,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        ($aa) := malloc (ty.I) [C 10];;
        (Index (V aa) (C ( 0))) := (C ( 44));;
        (Index (V aa) (C ( 1))) := (C (  1));;
        (Index (V aa) (C ( 2))) := (C ( 60));;
        (Index (V aa) (C ( 3))) := (- C (26));;
        (Index (V aa) (C ( 4))) := (C ( 54));;
        (Index (V aa) (C ( 5))) := (C ( 1));;
        (Index (V aa) (C ( 6))) := (C ( 92));;
        (Index (V aa) (C ( 7))) := (C ( 84));;
        (Index (V aa) (C ( 8))) := (C ( 38));;
        (Index (V aa) (C ( 9))) := (C ( 80));;
        $nn := (C ( 10));;
        ''bubblesort''![(V aa), (V nn)]
    \<rparr>"

definition p :: "fname \<Rightarrow> program"
  where "p mname \<equiv> 
    \<lparr> program.name = ''bubblesort'',
      program.structs = [],
      program.globals = (aa,ty.Ptr ty.I) # ints([nn]),
      program.functs = [bubblesort_decl, main_decl mname]
    \<rparr>"

definition "bubblesort_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code bubblesort_export}"../TestC" "bubblesort"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "bubblesort_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code bubblesort_test} "../TestC" "bubblesort_test"\<close>

end
