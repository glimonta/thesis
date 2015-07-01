theory Mod
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
      (* Modulo on positive integers resulting in zero *)
        aa ::= (Mod (Const 4) (Const 2));;
        (* Modulo on positive integers different from zero *)
        bb ::= (Mod (Const (7)) (Const (3)));;
        (* Modulo on negative integers with truncation towards zero *)
        cc ::= (Mod (Const (-8)) (Const (-3)));;
        (* Modulo on a postive and a negative integer with truncation towards zero *)
        dd ::= (Mod (Const (14)) (Const (-5)))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''mod'',
      program.globals = [aa,bb,cc,dd],
      program.procs = [main_decl]
    \<rparr>"

definition "mod_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code mod_export}"../TestC" "mod"\<close>

end
