theory CT_Quicksort
imports Test_Setup
begin

(* Swap: swaps two elements in an array, takes the address of the first element xx and the second 
   element yy and swaps their contents *)
definition swap_decl :: fun_decl
  where "swap_decl \<equiv> 
    \<lparr> fun_decl.name = ''swap'',
      fun_decl.rtype = None,
      fun_decl.params = int_ptrs [xx, yy],
      fun_decl.locals = ints [tt],
      fun_decl.body = 
        $tt := Deref (V xx);;
        ( *(V xx)) := (Deref (V yy));;
        ( *(V yy)) := (V tt)
    \<rparr>"

(* Quicksort: Takes an array a and its length n and returns the sorted array *)
definition quicksort_decl :: fun_decl
  where "quicksort_decl \<equiv> 
    \<lparr> fun_decl.name = ''quicksort'',
      fun_decl.rtype = None,
      fun_decl.params = int_ptrs [aa] @ ints [ss, ee],
      fun_decl.locals = ints [ll, rr, pp],
      fun_decl.body = 
        IF (Less (V ss) (V ee)) THEN (
          $ll := Plus (V ss) (Const 1);;
          $rr := V ee;;
          $pp := (Index (V aa) (V ss));;
          WHILE (Less (V ll) (V rr)) DO (
            IF (Less (Index (V aa) (V ll)) (Plus (V pp) (Const 1))) THEN
              $ll := (Plus (V ll) (Const 1))
            ELSE (
              IF (Less (V pp) (Index (V aa) (V rr))) THEN
                $rr := (Plus (V rr) (- Const (1)))
              ELSE (
                ''swap''!([(Ref (Indexl (V aa) (V ll))), (Ref (Indexl (V aa) (V rr)))])
              )  
            )
          );;
          IF (Less (Index (V aa) (V ll)) (V pp)) THEN (
            ''swap''!([(Ref (Indexl (V aa) (V ll))), (Ref (Indexl (V aa) (V ss)))]);;
            $ll := (Plus (V ll) (- Const (1)))
          ) ELSE (
            $ll := (Plus (V ll) (- Const (1)));;
            ''swap''!([(Ref (Indexl (V aa) (V ll))), (Ref (Indexl (V aa) (V ss)))])
          );;
          ''quicksort''!([V aa, V ss, V ll]);;
          ''quicksort''!([V aa, V rr, V ee])
        ) ELSE
          return
    \<rparr>"

definition main_decl 
  where "main_decl n \<equiv> 
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $aa := malloc ty.I [(Const ( 10))];;
        (Indexl (V aa) (Const ( 0))) := (Const (  4));;
        (Indexl (V aa) (Const ( 1))) := (Const ( 65));;
        (Indexl (V aa) (Const ( 2))) := (Const (  2));;
        (Indexl (V aa) (Const ( 3))) := (Const ( 31));;
        (Indexl (V aa) (Const ( 4))) := (Const (  0));;
        (Indexl (V aa) (Const ( 5))) := (Const ( 99));;
        (Indexl (V aa) (Const ( 6))) := (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) := (Const ( 83));;
        (Indexl (V aa) (Const ( 8))) := (Const (782));;
        (Indexl (V aa) (Const ( 9))) := (Const (  1));;
        $nn := (Const ( 10));;
        ''quicksort''!([(V aa), (Const 0), (V nn) - (Const (1))])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''quicksort'',
      program.structs = [],
      program.globals = [(aa, ty.Ptr ty.I), (nn,ty.I)],
      program.functs = [swap_decl, quicksort_decl, main_decl n]
    \<rparr>"

definition "quicksort_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code quicksort_export}"../TestC" "quicksort"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "quicksort_test"\<close>

end
