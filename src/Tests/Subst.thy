theory Subst
imports "../SmallStep" "Test"
begin

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= (Subst (Const 2) (Const 2));; (* Substraction positive values *)
        bb ::= (Subst (Const (-1)) (Const (-3)));; (* Substraction negative values *)
        cc ::= (New (Const 4));;
        dd ::= (Subst (Plus (V cc) (Const 2)) (Const 2));; (* Addition address + positive value - positive value *)
        ee ::= (Subst (Const (-2147483647)) (Const 4));; (* Overflow *)
        ff ::= (Div (Const 3) (Const 0))
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''plus'',
      program.globals = [aa,bb,cc,dd,ee,ff],
      program.procs = [main_decl]
    \<rparr>"

export_code p in SML

value "execute_show [] p"

definition "subst_ex \<equiv> (
  shows_prog p ''''
)"

ML_val {*
  val str = @{code subst_ex} |> String.implode;
  writeln str;
  val os = TextIO.openOut "/home/gabriela/Documents/thesis/src/TestC/subst_gen.c";
  TextIO.output (os, str);
  TextIO.flushOut os;
  TextIO.closeOut os;
*}

end