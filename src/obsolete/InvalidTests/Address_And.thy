theory Address_And
imports "../Tests/Test_Setup"
begin

definition "itf_template name c \<equiv> 
  \<lparr> fun_decl.name = name,
    fun_decl.rtype = None, 
    fun_decl.params = [],
    fun_decl.locals = int_ptrs [aa,bb] @ ints [ii,jj],
    fun_decl.body = 
      $aa := malloc ty.I [C 10];; 
      (FOR ii FROM C 0 TO C 10 DO $aa[$ii] := $ii);;
      $bb := malloc ty.I [C 20];;  
      $ii := C 10;;
      $jj := C 20;;
      c
  \<rparr>"

definition "it_template c \<equiv> 
  \<lparr> program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [itf_template ''main'' c]
  \<rparr>"

definition "exp_template_static c \<equiv> prepare_export (it_template c)"
definition "exp_template_dynamic c \<equiv> map_option fst (prepare_test_export (it_template c))"

definition "tests_static \<equiv> map exp_template_static [
  (* Invalid types for operations *)
  $ii := $aa && $bb,
  $ii := $aa && $ii,
  $ii := $ii && $aa,

  $ii := $aa || $bb,
  $ii := $aa || $ii,
  $ii := $ii || $aa,

  $ii := $aa / $bb,
  $ii := $aa / $ii,
  $ii := $ii / $aa,

  $ii := $aa % $bb,
  $ii := $aa % $ii,
  $ii := $ii % $aa,

  $ii := $aa * $bb,
  $ii := $aa * $ii,
  $ii := $ii * $aa,

  $ii := $aa <= $ii,
  $ii := $ii <= $aa,

  $ii := $aa == $ii,
  $ii := $ii == $aa,

  $ii := ! $aa,
  $ii := - $aa,

  $ii := Null && $ii,
  $ii := $ii && Null,

  $ii := Null || $ii,
  $ii := $ii || Null,

  $ii := Null / $ii,
  $ii := $ii / Null,

  $ii := Null % $ii,
  $ii := $ii % Null,

  $ii := Null * $ii,
  $ii := $ii * Null,

  $ii := Null <= $ii,
  $ii := $ii <= Null,

  $ii := Null == $ii,
  $ii := $ii == Null,

  $ii := Null + $ii,
  $ii := $ii + Null,

  $ii := Null - $ii,
  $ii := $ii - Null,

  $bb := malloc ty.I [$aa],
  free $ii,
  $ii := $aa[$bb],

  $ii := *$jj,
  $ii := $jj[$ii],

  $uu := C 42, (* Undeclared uu *)

  (* Constant overflows *)
  $ii := C (plus INT_MAX 1),
  $ii := C (minus INT_MIN 1)

]"

ML \<open>map expect_failed_test @{code tests_static}\<close>

definition "tests_dynamic \<equiv> map exp_template_dynamic [
  $ii := $bb[C 0],    (* Uninitialized *)
  $ii := $aa[($ii)],  (* Out of bounds *)
  $ii := $aa[($ii + C 1)], (* Out of bounds *)
  free ($aa + C 1), (* Not base address of block *)
  free ($aa);; free $aa, (* Double-free *)
  $aa := malloc ty.I [C 0], (* Zero-size malloc *)
  $aa := malloc ty.I [C (uminus 5)], (* Negative malloc *)
  $aa := Null;; $ii := $aa[C 0], (* Null-pointer deref *)
  $aa := Null;; $ii := *$aa, (* Null-pointer deref *)
  $aa := Null;; $ii := $aa[C 1], (* Null + 1 - pointer deref *)
  $ii := C 0;; WHILE $ii<=$jj DO ($bb[$ii] := C 0;; $ii := $ii + C 1), (* Off by one: A pretty common error pattern *)
  (* Overflows *)
  $ii := C INT_MAX + C 1,
  $ii := C INT_MIN - C 1,
  $ii := - C INT_MIN,
  $ii := C INT_MAX * C 2,
  $ii := C INT_MIN / (- C 1),
  (* Div by zero *)
  $ii := C 42 / C 0,
  $ii := C 42 % C 0


]"

xxx
  rename file
  add reserved keywords
  add function arguments
  add structs (zero-size struct, direct and indirect array of zero-size elements)
  add dup-names (in globals, locals, args, structs)

ML \<open>map expect_failed_test @{code tests_dynamic}\<close>


definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.rtype = None, fun_decl.params = [],
      fun_decl.locals = int_ptrs [aa,bb],
      fun_decl.body =
        $aa := malloc ty.I [C 21];; 
        $bb := malloc ty.I [C 21];; 
        $xx := ($aa && $bb)
        (* Cannot perform and between 2 addresses *)
    \<rparr>"

definition p :: program
  where "p \<equiv>
    \<lparr> program.name = ''address_and'',
      program.structs = [], program.globals = ints [xx],
      program.functs = [main_decl]
    \<rparr>"

definition "test \<equiv> prepare_test_export p"
ML \<open>expect_failed_test @{code test}\<close>

end
