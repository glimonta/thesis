theory Occurs
imports Test_Setup
begin

(* Occurs: Takes an array a, its length n and an element x, returns 0 if the element x doesn't exist
   in the array and 1 if it does exist. *)
definition occurs_decl :: fun_decl
  where "occurs_decl \<equiv> 
    \<lparr> fun_decl.name = ''occurs'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = [(aa,ty.Ptr ty.I)]@ints [nn, xx],
      fun_decl.locals = ints [cc, ii],
      fun_decl.body = 
        $cc := (Const ( 0));; (* Counter of occurences *)
        $ii := C 0;;

        WHILE ($ii < $nn && !$cc) DO (
          IF $aa[$ii] == $xx THEN $cc := $cc + C 1 ELSE $ii := $ii + C 1
        );;  
        return $cc
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

        $xx := Const 5;;
        $yy := Const 84;;

        $foo := ''occurs''!([(V aa), (V nn), V xx]);;
        $bar := ''occurs''!([(V aa), (V nn), V yy])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''occurs'',
      program.structs = [],
      program.globals = [(aa,ty.Ptr ty.I)] @ ints [nn, xx, yy, foo, bar],
      program.functs = [occurs_decl, main_decl n]
    \<rparr>"

definition "occurs_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code occurs_export}"../TestC" "occurs"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "occurs_test"\<close>

end
