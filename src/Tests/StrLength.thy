theory StrLength
imports "../SmallStep" Test "../Test_Harness"
begin

(* Takes a number n and returns an array of length n + 1 initialized with numbers from 1 to n in
  its [0,n] positions *)
definition create_array_decl :: fun_decl
  where "create_array_decl \<equiv> 
    \<lparr> fun_decl.name = ''create_array'',
      fun_decl.params = [nn],
      fun_decl.locals = [pp, ii],
      fun_decl.body = 
        pp ::= New (Plus (V nn) (Const (1)));;
        ii ::= Const (0);;
        WHILE (Less (V ii) (V nn)) DO (
          (Indexl (V pp) (V ii)) ::== (Plus (V ii) (Const (1)));;
          ii ::= Plus (V ii) (Const (1))
          );;
        (Indexl (V pp) (V ii)) ::== (Const ( 0)) ;;
        Return (V pp)
    \<rparr>"

(* Strlength: Takes an array (ending in 0) and returns the length of the array *)
definition str_len_decl :: fun_decl
  where "str_len_decl \<equiv> 
    \<lparr> fun_decl.name = ''str_len'',
      fun_decl.params = [aa],
      fun_decl.locals = [pp, ll],
      fun_decl.body = 
        pp ::= (V aa);;
        ll ::= Const ( 0);;
        WHILE (Deref (V pp)) DO (
          ll ::= Plus (V ll) (Const ( 1));;
          pp ::= (Ref (Indexl (V pp) (Const (1)))) (* Size of signed long *)
          );;
        Return (V ll)
    \<rparr>"

value "plus_val (A (0,0)) (I 8)"

definition main_decl :: fun_decl
  where "main_decl \<equiv> 
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        Callfun aa ''create_array'' [(Const 5)];;
        Callfun ll ''str_len'' [V aa]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''strlen'',
      program.globals = [aa, ll],
      program.procs = [create_array_decl, str_len_decl, main_decl]
    \<rparr>"

export_code p in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p"

definition "strlen_exec \<equiv> execute_show [] p"

definition "strlen \<equiv> (
  shows_prog p ''''
)"

definition "strlen_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code strlen_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code strlen} "../TestC" "strlen"\<close>

end
