theory Basic_Ops
imports Test_Setup
begin

definition test_decl :: fun_decl where
  "test_decl \<equiv> 
    \<lparr> fun_decl.name = ''test'',
      fun_decl.rtype = None,
      fun_decl.params = ints [vv],
      fun_decl.locals = [],
      fun_decl.body = 
        $rr[$ii] := $vv;;
        $ii := $ii + C 1
    \<rparr>"

definition testptr_decl :: fun_decl where
  "testptr_decl \<equiv> 
    \<lparr> fun_decl.name = ''testptr'',
      fun_decl.rtype = None,
      fun_decl.params = int_ptrs [vv],
      fun_decl.locals = [],
      fun_decl.body = 
        $ss[$jj] := $vv;;
        $jj := $jj + C 1
    \<rparr>"


definition "and_test \<equiv> 
  ''test''![$ff && $ff];;
  ''test''![$ff && $tt];;
  ''test''![$tt && $ff];;
  ''test''![$tt && $tt];;

  ''test''![$ff && $ff];;
  ''test''![$ff && C 3];;
  ''test''![C 4 && $ff];;
  ''test''![C 1 && C 2]
  "

definition "or_test \<equiv> 
  ''test''![$ff || $ff];;
  ''test''![$ff || $tt];;
  ''test''![$tt || $ff];;
  ''test''![$tt || $tt];;
  ''test''![$ff || $ff];;
  ''test''![$ff || C 3];;
  ''test''![C 4 || $ff];;
  ''test''![C 1 || C 2]
"

definition "not_test \<equiv> 
  ''test''![!$ff];;
  ''test''![!$tt];;
  ''test''![!C 5]"

definition "bnot_test \<equiv> 
  ''test''![~C 0];;
  ''test''![~C 7];;
  ''test''![~C (uminus 1)];;
  ''test''![~C INT_MAX];;
  ''test''![~C INT_MIN]
"

definition "band_test \<equiv> 
  ''test''![C 3 & C 7];;
  ''test''![C 81 & C INT_MIN];;
  ''test''![C 81 & - C 1]
  "

definition "bor_test \<equiv> 
  ''test''![C 3 | C 7];;
  ''test''![C 81 | C INT_MIN];;
  ''test''![C 81 | - C 1]
  "

definition "bxor_test \<equiv> 
  ''test''![C 3 ^ C 7];;
  ''test''![C 81 ^ C INT_MIN];;
  ''test''![C 81 ^ - C 1]"


definition "div_test \<equiv> 
  (* Division on positive integers that can be exactly divided *)
  ''test''![(Div (Const 4) (Const 2))];;
  (* Division on positive integers that can't be exactly divided *)
  ''test''![(Div (Const (7)) (Const (4)))];;
  (* Division on negative integers with truncation towards zero *)
  ''test''![(Div (-Const (8)) (-Const (3)))];;
  (* Division on a postive and a negative integer with truncation towards zero *)
  ''test''![(Div (Const (14)) (-Const (5)))]"

definition "less_test \<equiv> 
  ''test''![(Less (Const 2) (Const 89))];;
  ''test''![(Less (-Const (7)) (-Const (4)))];;
  ''test''![(Less (-Const (8)) (Const (3)))];;
  ''test''![(Less (Const (14)) (-Const (5)))];;
  ''test''![(Less (Const 42) (Const 4))];;
  ''test''![(Less (-Const (4)) (-Const (56)))];;
  ''test''![(Less (Const 42) (Const 42))]
"

definition "leq_test \<equiv> 
  ''test''![(Leq(Const 2) (Const 89))];;
  ''test''![(Leq (-Const (7)) (-Const (4)))];;
  ''test''![(Leq (-Const (8)) (Const (3)))];;
  ''test''![(Leq (Const (14)) (-Const (5)))];;
  ''test''![(Leq (Const 42) (Const 4))];;
  ''test''![(Leq (-Const (4)) (-Const (56)))];;
  ''test''![(Leq (Const 42) (Const 42))]
"

definition "less_ptr_test \<equiv> 
        ''test''![$aa < $aa];;
        ''test''![$aa < $bb];;
        ''test''![$aa < $cc];;
        
        ''test''![$bb < $aa];;
        ''test''![$bb < $bb];;
        ''test''![$bb < $cc];;

        ''test''![$cc < $aa];;
        ''test''![$cc < $bb];;
        ''test''![$cc < $cc]"

definition "leq_ptr_test \<equiv> 
        ''test''![$aa <= $aa];;
        ''test''![$aa <= $bb];;
        ''test''![$aa <= $cc];;
                      
        ''test''![$bb <= $aa];;
        ''test''![$bb <= $bb];;
        ''test''![$bb <= $cc];;
                      
        ''test''![$cc <= $aa];;
        ''test''![$cc <= $bb];;
        ''test''![$cc <= $cc]"

definition lessleq_test_decl :: fun_decl where
  "lessleq_test_decl \<equiv> 
    \<lparr> fun_decl.name = ''lessleq_test'',
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = int_ptrs [aa,bb,cc],
      fun_decl.body = (
        $aa := malloc ty.I [Const 10];;
        $bb := (Plus (V aa) (Const 2));;
        $cc := (Plus (V aa) (Const 10));;

        less_test;;
        leq_test;;
        less_ptr_test;;
        leq_ptr_test
      )
    \<rparr>"


definition eq_test_decl :: fun_decl where
  "eq_test_decl \<equiv> 
    \<lparr> fun_decl.name = ''eq_test'',
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = int_ptrs [aa,bb,cc],
      fun_decl.body = (
        $aa := malloc ty.I [Const 10];;
        $bb := malloc ty.I [Const 10];;
        $cc := (Plus (V aa) (Const 2));;

        (* True, two integers*)
          ''test''![(Eq (Const 42) (Const 42))];;
        (* False, two integers *)
          ''test''![(Eq (Const 0) (Const 23))];;
        (* True, two addresses *)
          ''test''![(Eq (V aa) (V aa))];;
        (* False, two addresses *)
          ''test''![(Eq (V aa) (V cc))];;
        (* False, two addresses *)
          ''test''![(Eq (V aa) (V bb))];;
        (* False, two addresses *)
          ''test''![(Eq (V cc) (V bb))]
      )
    \<rparr>"


definition "uminus_test \<equiv> 
  ''test''![-C 42];;
  ''test''![-(-(C 1))];;
  ''test''![-(C INT_MAX)];;
  ''test''![-(C INT_MAX) - C 1]
"

definition "mod_test \<equiv> 
  (* Modulo on positive integers resulting in zero *)
  ''test''![(Mod (Const 4) (Const 2))];;
  (* Modulo on positive integers different from zero *)
  ''test''![(Mod (Const (7)) (Const (3)))];;
  (* Modulo on negative integers with truncation towards zero *)
  ''test''![(Mod (-Const (8)) (-Const (3)))];;
  (* Modulo on a positve and a negative integer with truncation towards zero *)
  ''test''![(Mod (Const (14)) (-Const (5)))];;

  ''test''![(Mod (Const (INT_MIN)) (Const (7)))];;

  ''test''![(Mod (Const (INT_MAX)) (Const (7)))];;

  ''test''![(Mod (Const (INT_MIN)) (Const (INT_MAX)))];;

  ''test''![(Mod (Const (INT_MAX)) (Const (INT_MIN)))];;

  ''test''![(Mod (Const (INT_MIN)) (Const (INT_MIN)))]
"

definition "mult_test \<equiv> 
  (* Multiplication on positive integers *)
    ''test''![(Mult (Const 4) (Const 2))];;
  (* Multiplication on negative integers *)
    ''test''![(Mult (-Const (7)) (-Const (4)))];;
  (* Multiplication on a positive and a negative integer *)
    ''test''![(Mult (-Const (8)) (Const (3)))];;
  (* Multiplication on a negative and a positive integer *)
    ''test''![(Mult (Const (14)) (-Const (5)))];;
  (* Multiplication by zero *)
    ''test''![(Mult (Const 42) (Const 0))];;
    ''test''![(Mult (Const 0) (Const 42))]
"


definition plus_test_decl :: fun_decl where
  "plus_test_decl \<equiv> 
    \<lparr> fun_decl.name = ''plus_test'',
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = int_ptrs [aa,cc],
      fun_decl.body = (
        $aa := malloc ty.I [Const 10];;
        $cc := (Plus (V aa) (Const 4));;

        ''test''![(Plus (Const 2) (Const 2))];; (* Addition positive values *)
        ''test''![(Plus (Const (uminus 1)) (Const (uminus 3)))];; (* Addition negative values *)
        ''test''![(Plus (Const (uminus 3)) (Const (2)))];; (* Addition negative + postive = negative *)
        ''test''![(Plus (Const (3)) (Const (uminus 2)))];; (* Addition postive + negative = positive *)
        ''test''![(Plus (Const (uminus 3)) (Const (5)))];; (* Addition negative + postive = positive *)
        ''test''![(Plus (Const (3)) (Const (uminus 6)))];; (* Addition postive + negative = negative *)
        ''testptr''![(Plus (V aa) (Const 4))];; (* Addition address + positive value *)
        ''testptr''![(Plus (V aa) (Const 10))];; (* Addition address + positive value *)
        ''testptr''![(Plus (V cc) (Const (uminus 2)))] (* Addition address + negative value *)
      )
    \<rparr>"

definition minus_test_decl :: fun_decl where
  "minus_test_decl \<equiv> 
    \<lparr> fun_decl.name = ''minus_test'',
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = int_ptrs [aa,cc],
      fun_decl.body = (
        $aa := malloc ty.I [Const 10];;
        $cc := (Plus (V aa) (Const 4));;

        ''test''![C 2 - C 2];;     
        ''test''![-C 1 - (-C 3)];; 
        ''test''![-C 3 - C 2];;
        ''test''![C 3 - (-C 2)];;

        ''test''![$cc - $aa];;
        ''test''![$cc - $cc];;
        ''test''![$aa - $cc];;

        ''test''![&(($aa)[C 10]) - $aa]
      )
    \<rparr>"



definition refderef_test_decl :: fun_decl where
  "refderef_test_decl \<equiv> 
    \<lparr> fun_decl.name = ''refderef_test'',
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = int_ptrs [aa,cc]@ints[bb],
      fun_decl.body = (
        $aa := malloc ty.I [Const 10];;
        $aa[C 5] := C 9;;

        $cc := &$bb;;  (* Pointer to local variable *)
        $bb := C 3;;
        
        ''test''![*$cc];;
        ''test''![$aa[C 5]];;
        ''test''![*(&($aa[C 2]) + C 3)]
      )
    \<rparr>"


definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = ints [tt,ff],
      fun_decl.body = (
        $rr := malloc ty.I [C 1000];;
        $ii := C 0;;

        $ss := malloc (ty.Ptr ty.I) [C 1000];;
        $jj := C 0;;

        $tt := C 1;;
        $ff := C 0;;

        ''refderef_test''![];;
        uminus_test;;
        not_test;;
        bnot_test;;

        div_test;;
        mod_test;;
        mult_test;;

        ''plus_test''![];;
        ''minus_test''![];;

        ''lessleq_test''![];;
        ''eq_test''![];;

        and_test;; 
        or_test;; 

        band_test;; 
        bor_test;; 
        bxor_test
      )  
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''basic_ops'',
      program.structs = [],
      program.globals = int_ptrs [rr] @ [(ss,ty.Ptr (ty.Ptr ty.I))] @ ints [ii,jj],
      program.functs = [lessleq_test_decl,refderef_test_decl,minus_test_decl,plus_test_decl,eq_test_decl,testptr_decl,test_decl,main_decl n]
    \<rparr>"

definition "less_export \<equiv> prepare_export (p ''main'')"

value "export_shows (p ''main'') ''''"


setup \<open>export_c_code @{code less_export}"../TestC" "basic_ops"\<close>
definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "basic_ops_test"\<close>

end
