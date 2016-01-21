theory Count
imports "Test_Setup"
begin

(* Count: Takes an array a, its length n and an element x, returns the number of occurences of x
    in a. *)
definition count_decl :: fun_decl
  where "count_decl \<equiv>
    \<lparr> fun_decl.name = ''count'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = (aa,ty.Ptr ty.I) # ints [nn, xx],
      fun_decl.locals = ints [cc, ii],
      fun_decl.body = 
        $cc := (C 0);; (* Counter of occurences *)
        FOR ii FROM (C ( 0)) TO (V nn) DO
          (IF (Eq (Index (V aa) (V ii)) (V xx))
            THEN $cc := (Plus (V cc) (C ( 1)))
          ELSE SKIP);;
        return (V cc)
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $aa := malloc (ty.I) [Const (10)];;
        (Indexl (V aa) (Const ( 0))) := (Const ( 44));;
        (Indexl (V aa) (Const ( 1))) := (Const ( 98));;
        (Indexl (V aa) (Const ( 2))) := (Const ( 44));;
        (Indexl (V aa) (Const ( 3))) := (Const ( 44));;
        (Indexl (V aa) (Const ( 4))) := (Const ( 54));;
        (Indexl (V aa) (Const ( 5))) := (Const ( 1));;
        (Indexl (V aa) (Const ( 6))) := (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) := (Const ( 84));;
        (Indexl (V aa) (Const ( 8))) := (Const ( 44));;
        (Indexl (V aa) (Const ( 9))) := (Const ( 44));;
        $nn := (Const ( 10));;
    
        $foo := ''count''!([(V aa), (V nn), Const 5]);;
        $bar := ''count''!([(V aa), (V nn), Const 84]);;
        $baz := ''count''!([(V aa), (V nn), Const 44])
    \<rparr>"

definition p 
  where "p n \<equiv> 
    \<lparr> program.name = ''count'',
      program.structs = [],
      program.globals = (aa,ty.Ptr ty.I)# ints [nn, foo, bar, baz],
      program.functs = [count_decl, main_decl n]
    \<rparr>"

definition "count_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code count_export}"../TestC" "count"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "count_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code count_test} "../TestC" "count_test"\<close>

end
