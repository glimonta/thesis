theory Returnv
imports Test_Setup
begin


(* Even though there's no explicit return in the plus function it will return because
   a function returns when reaching the end of control *)
definition plus_foo_decl :: fun_decl
  where "plus_foo_decl \<equiv>
    \<lparr> fun_decl.name = ''plus_foo'',
      fun_decl.rtype = None,
      fun_decl.params = ints [ii],
      fun_decl.locals = [],
      fun_decl.body = 
        $foo := Plus (V foo) (V ii)
    \<rparr>"                                

(* We can also use a explicit return and it works the same way *)
definition plus_one_foo_decl :: fun_decl
  where "plus_one_foo_decl \<equiv>
    \<lparr> fun_decl.name = ''plus_one_foo'',
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $foo := Plus (V foo) (Const 1);; return
    \<rparr>"  

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $foo := Const 21;;
        ''plus_foo''!([(Const 20)]);;
        ''plus_one_foo''!([]);;
        IF (Eq (V foo) (Const 42)) THEN
          $bar := Const 1 (* If it's correct then we set bar to true *)
        ELSE
          $bar := (Plus (Const INT_MAX) (Const 1)) (* Otherwise we generate an error in the program *)
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''returnv'',
      program.structs = [],
      program.globals = ints [foo, bar],
      program.functs = [plus_foo_decl, plus_one_foo_decl, main_decl n]
    \<rparr>"

definition "returnv_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code returnv_export}"../TestC" "returnv"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "returnv_test"\<close>

end
