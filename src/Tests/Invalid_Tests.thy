section \<open>Tests that are expected to fail\<close>
theory Invalid_Tests
imports "../Tests/Test_Setup"
begin

subsection \<open>Templates\<close>

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

(* Regression tests for templates: With SKIP, they must not fail *)
ML \<open>
  if @{code exp_template_static} @{code SKIP} = NONE then
    error "Expected Some"
  else ()  
\<close>

ML \<open>
  if @{code exp_template_dynamic} @{code SKIP} = NONE then
    error "Expected Some"
  else ()  
\<close>

subsection \<open>Static Errors\<close>
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

subsubsection \<open>Keywords\<close>
definition "kws \<equiv> [ 
  ''auto''          ,
  ''_Bool''         ,
  ''break''         ,
  ''case''          ,
  ''char''          ,
  ''_Complex''      ,
  ''const''         ,
  ''continue''      ,
  ''default''       ,
  ''double''        ,
  ''else''          ,
  ''enum''          ,
  ''extern''        ,
  ''for''           ,
  ''goto''          ,
  ''if''            ,
  ''_Imaginary''    ,
  ''inline''        ,
  ''int''           ,
  ''long''          ,
  ''register''      ,
  ''return''        ,
  ''short''         ,
  ''signed''        ,
  ''sizeof''        ,
  ''static''        ,
  ''struct''        ,
  ''switch''        ,
  ''typedef''       ,
  ''union''         ,                                     
  ''unsigned''      ,
  ''void''          ,
  ''volatile''      ,
  ''while'' 
]"


definition "kwprog1 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [\<lparr>struct_decl.name = k, struct_decl.members = [(aa,ty.I)]\<rparr>], 
    program.globals = [],
    program.functs = [itf_template ''main'' SKIP]
  \<rparr>"

definition "kwprog2 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [\<lparr>struct_decl.name = aa, struct_decl.members = [(k,ty.I)]\<rparr>], 
    program.globals = [],
    program.functs = [itf_template ''main'' SKIP]
  \<rparr>"

definition "kwprog3 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [(k,ty.I)],
    program.functs = [itf_template ''main'' SKIP]
  \<rparr>"

definition "kwprog4 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = k, 
        fun_decl.rtype = None, 
        fun_decl.params = [], 
        fun_decl.locals = [], 
        fun_decl.body = SKIP\<rparr>,
      itf_template ''main'' SKIP]
  \<rparr>"

definition "kwprog5 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = ''f'', 
        fun_decl.rtype = None, 
        fun_decl.params = [(k,ty.I)], 
        fun_decl.locals = [], 
        fun_decl.body = SKIP\<rparr>,
      itf_template ''main'' SKIP]
  \<rparr>"

definition "kwprog6 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = ''f'', 
        fun_decl.rtype = None, 
        fun_decl.params = [], 
        fun_decl.locals = [(k,ty.I)], 
        fun_decl.body = SKIP\<rparr>,
      itf_template ''main'' SKIP]
  \<rparr>"

definition "kw_tests \<equiv> map prepare_export (concat (map (\<lambda>k. map k kws) 
  [kwprog1,kwprog2,kwprog3,kwprog4,kwprog5,kwprog6]))"

ML \<open>map expect_failed_test @{code kw_tests}\<close>

definition "kw_test_regression \<equiv> map prepare_export (((map (\<lambda>k. k ''valid_name'') 
  [kwprog1,kwprog2,kwprog3,kwprog4,kwprog5,kwprog6])))"

ML \<open>
  map (fn x => if x=NONE then error "Expected SOME" else ()) @{code kw_test_regression}
\<close>

subsubsection \<open>Function arguments\<close>

definition "funarg1 \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = ''f'', 
        fun_decl.rtype = None, 
        fun_decl.params = [], 
        fun_decl.locals = [], 
        fun_decl.body = SKIP\<rparr>,
      itf_template ''main'' (''f''![C 42])]
  \<rparr>"

definition "funarg2 \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = ''f'', 
        fun_decl.rtype = None, 
        fun_decl.params = [(aa,ty.I)], 
        fun_decl.locals = [], 
        fun_decl.body = SKIP\<rparr>,
      itf_template ''main'' (''f''![])]
  \<rparr>"


definition "funarg_tests \<equiv> map prepare_export [funarg1,funarg2]"
ML \<open>map expect_failed_test @{code funarg_tests}\<close>

subsubsection \<open>Zero-size structs\<close>
definition "structs_tests1 \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [\<lparr>struct_decl.name = ''s'', struct_decl.members = []\<rparr>], 
    program.globals = [],
    program.functs = [
      itf_template ''main'' (''f''![])]
  \<rparr>"

definition "structs_tests2 \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [\<lparr>
      struct_decl.name = ''s'', 
      struct_decl.members = [(''x'',ty.Array 5 (ty.Array 0 ty.I))]\<rparr>], 
    program.globals = [],
    program.functs = [
      itf_template ''main'' (''f''![])]
  \<rparr>"


definition "structs_tests \<equiv> map prepare_export [structs_tests1,structs_tests2]"
ML \<open>map expect_failed_test @{code structs_tests}\<close>

subsubsection \<open>Duplicate Names\<close>
definition "dupprog1 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [
      \<lparr>struct_decl.name = k, struct_decl.members = [(aa,ty.I)]\<rparr>,
      \<lparr>struct_decl.name = k, struct_decl.members = [(bb,ty.I)]\<rparr>
      ], 
    program.globals = [],
    program.functs = [itf_template ''main'' SKIP]
  \<rparr>"

definition "dupprog2 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [\<lparr>struct_decl.name = aa, 
      struct_decl.members = [(k,ty.I),(k,ty.Ptr ty.I)]\<rparr>], 
    program.globals = [],
    program.functs = [itf_template ''main'' SKIP]
  \<rparr>"

definition "dupprog3 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [(k,ty.I),(k,ty.Ptr ty.I)],
    program.functs = [itf_template ''main'' SKIP]
  \<rparr>"

definition "dupprog4 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = k, 
        fun_decl.rtype = None, 
        fun_decl.params = [], 
        fun_decl.locals = [], 
        fun_decl.body = SKIP\<rparr>,
      \<lparr>
        fun_decl.name = k, 
        fun_decl.rtype = Some ty.I, 
        fun_decl.params = [], 
        fun_decl.locals = [], 
        fun_decl.body = return (C 42)\<rparr>,
      itf_template ''main'' SKIP]
  \<rparr>"

definition "dupprog5 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = ''f'', 
        fun_decl.rtype = None, 
        fun_decl.params = [(k,ty.I),(k,ty.Ptr ty.I)], 
        fun_decl.locals = [], 
        fun_decl.body = SKIP\<rparr>,
      itf_template ''main'' SKIP]
  \<rparr>"

definition "dupprog6 k \<equiv>  \<lparr> 
    program.name = ''invalid_test'',
    program.structs = [], 
    program.globals = [],
    program.functs = [
      \<lparr>
        fun_decl.name = ''f'', 
        fun_decl.rtype = None, 
        fun_decl.params = [], 
        fun_decl.locals = [(k,ty.I), (k,ty.Ptr ty.I)], 
        fun_decl.body = SKIP\<rparr>,
      itf_template ''main'' SKIP]
  \<rparr>"

definition "dup_tests \<equiv> map prepare_export ((map (\<lambda>k. k ''name'') 
  [dupprog1,dupprog2,dupprog3,dupprog4,dupprog5,dupprog6]))"

ML \<open>map expect_failed_test @{code dup_tests}\<close>






subsection \<open>Dynamic Errors\<close>

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

ML \<open>map expect_failed_test @{code tests_dynamic}\<close>



end
