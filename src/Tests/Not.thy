theory Not
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        ''true'' ::= Const 1;;
        ''false'' ::= Const 0;;
      (* True \<rightarrow> False*)
        aa ::= (Not (V ''true''));;
      (* False \<rightarrow> True*)
        bb ::= (Not (V ''false''))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''not'',
      program.globals = [aa,bb,''true'',''false''],
      program.procs = [main_decl]
    \<rparr>"

definition "not_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code not_export}"../TestC" "not"\<close>

end
