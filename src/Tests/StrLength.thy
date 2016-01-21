theory StrLength
imports Test_Setup
begin

(* Takes a number n and returns an array of length n + 1 initialized with numbers from 1 to n in
  its [0,n] positions *)
definition create_array_decl :: fun_decl
  where "create_array_decl \<equiv> 
    \<lparr> fun_decl.name = ''create_array'',
      fun_decl.rtype = Some (ty.Ptr ty.I),
      fun_decl.params = ints [nn],
      fun_decl.locals = [(pp,ty.Ptr ty.I), (ii,ty.I)],
      fun_decl.body = 
        $pp := malloc ty.I [(Plus (V nn) (Const (1)))];;
        $ii := Const (0);;
        WHILE (Less (V ii) (V nn)) DO (
          (Indexl (V pp) (V ii)) := (Plus (V ii) (Const (1)));;
          $ii := Plus (V ii) (Const (1))
          );;
        (Indexl (V pp) (V ii)) := (Const ( 0)) ;;
        return (V pp)
    \<rparr>"

(* Strlength: Takes an array (ending in 0) and returns the length of the array *)
definition str_len_decl :: fun_decl
  where "str_len_decl \<equiv> 
    \<lparr> fun_decl.name = ''str_len'',
      fun_decl.rtype = Some ty.I,
      fun_decl.params = int_ptrs [aa],
      fun_decl.locals = [(pp,ty.Ptr ty.I), (ll,ty.I)],
      fun_decl.body = 
        $pp := (V aa);;
        $ll := Const ( 0);;
        WHILE (Deref (V pp)) DO (
          $ll := Plus (V ll) (Const ( 1));;
          $pp := (Ref (Indexl (V pp) (Const (1)))) (* Size of signed long *)
          );;
        return (V ll)
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv> 
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $aa := ''create_array''!([(Const 5)]);;
        $ll := ''str_len''!([V aa])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''strlen'',
      program.structs = [],
      program.globals = [(aa,ty.Ptr ty.I), (ll,ty.I)],
      program.functs = [create_array_decl, str_len_decl, main_decl n]
    \<rparr>"

definition "strlen_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code strlen_export}"../TestC" "strlen"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "strlen_test"\<close>


end
