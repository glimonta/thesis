theory Deref
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition init_decl :: fun_decl
  where "init_decl \<equiv>
    \<lparr> fun_decl.name = ''init'',
      fun_decl.params = [aa, nn],
      fun_decl.locals = [ii],
      fun_decl.body = 
        ii ::= Const 0;;
        WHILE (Less (V ii) (V nn)) DO (
          (Indexl (V aa) (V ii)) ::== (V ii);;
          ii ::= (Plus (V ii) (Const 1))
        )
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        nn ::= Const 10;;
        aa ::= New (V nn);;

        Callfunv ''init'' [V aa, V nn];;

        (* j contains the number of matches with the content in memory *)
        ii ::= Const 0;;
        jj ::= Const 0;;
        WHILE (Less (V ii) (V nn)) DO (
          (IF (Eq (Deref (Plus (V aa) (V ii))) (V ii)) THEN
            jj ::= (Plus (V jj) (Const 1))
          ELSE
            SKIP);;
          ii ::= (Plus (V ii) (Const 1))
        )
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''deref'',
      program.globals = [nn,aa,ii,jj],
      program.procs = [init_decl, main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "deref_exec \<equiv> execute_show [] p"

definition "deref_ex \<equiv> (
  shows_prog p ''''
)"

definition "deref_test \<equiv> do {
  s \<leftarrow> execute p;
  let vnames = program.globals p;
  (_,tests) \<leftarrow> emit_globals_tests vnames s;
  let vars = tests_variables tests 1 '''';
  let instrs = tests_instructions tests 1 '''';
  Some (vars, instrs)
}"


ML_val \<open> @{code deref_test} |> the |> apply2 String.implode |> apply2 writeln \<close>

setup \<open>export_c_code @{code deref_ex} @{code deref_exec} "../TestC" "deref"\<close>


end