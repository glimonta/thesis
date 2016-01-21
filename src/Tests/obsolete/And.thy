theory And
imports "../Syntax/Pretty_Program" Test_Setup
begin

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $''true'' := C 1;;
        $''false'' := C 0;;
      (* True *)
        $aa := (And (V ''true'') (V ''true''));;
      (* False *)
        $bb := (And (V ''true'') (V ''false''));;
      (* False (short-circuit evaluation) *)
        $cc := (And (V ''false'') (V ''true''));;
      (* False *)
        $dd := (And (V ''false'') (V ''false''))
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''and'',
      program.structs = [],
      program.globals = ints [aa,bb,cc,dd,''true'',''false''],
      program.functs = [main_decl n]
    \<rparr>"

definition "and_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code and_export}"../TestC" "and"\<close>

end
