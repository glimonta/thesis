theory Plus
imports "../SmallStep" "Test"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Plus (Const 2) (Const 2));; (* Addition positive values *)
        bb ::= (Plus (Const (-1)) (Const (-3)));; (* Addition negative values *)
        cc ::= (New (Const 4));;
        dd ::= (Plus (V cc) (Const 2)) (* Addition address + positive value *)
        (*ee ::= (Plus (Const 2147483647) (Const 1)) (* Overflow *)*)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''plus'',
      program.globals = [aa,bb,cc,dd,ee],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

(*
definition execute :: "program \<Rightarrow> state option" where
  "execute p \<equiv> do {
    assert (valid_program p);
    interp (proc_table_of p) (initial_state p)
  }"
*)
definition "plus_ex \<equiv> (
  shows_prog p ''''
)"

ML_val {*
  val str = @{code plus_ex} |> String.implode;
  writeln str;
  val os = TextIO.openOut "/home/gabriela/Documents/thesis/src/TestC/plus_gen.c";
  TextIO.output (os, str);
  TextIO.flushOut os;
  TextIO.closeOut os;
*}

end