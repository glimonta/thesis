theory Minimum
imports "../SmallStep" Test
begin

(* Min: Takes an array a and its length n and returns the minimum element of the array *)
definition min_decl :: fun_decl
  where "min_decl \<equiv>
    \<lparr> fun_decl.name = ''min'',
      fun_decl.params = [aa, nn],
      fun_decl.locals = [ii, mm],
      fun_decl.body = 
        mm ::= (Index (V aa) (Const 0));;
        FOR ii FROM (Const ( 0)) TO (Plus (V nn) (Const ( -1))) DO
          (IF (Less (Index (V aa) (V ii)) (V mm))
            THEN mm ::= (Index (V aa) (V ii))
          ELSE SKIP);;
          Return (V mm)
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= New (Const ( 10));;
        (Indexl (V aa) (Const ( 0))) ::== (Const ( 44));;
        (Indexl (V aa) (Const ( 1))) ::== (Const ( 98));;
        (Indexl (V aa) (Const ( 2))) ::== (Const ( 60));;
        (Indexl (V aa) (Const ( 3))) ::== (Const ( 26));;
        (Indexl (V aa) (Const ( 4))) ::== (Const ( 54));;
        (Indexl (V aa) (Const ( 5))) ::== (Const ( 1));;
        (Indexl (V aa) (Const ( 6))) ::== (Const ( 92));;
        (Indexl (V aa) (Const ( 7))) ::== (Const ( 84));;
        (Indexl (V aa) (Const ( 8))) ::== (Const ( 38));;
        (Indexl (V aa) (Const ( 9))) ::== (Const ( 80));;
        nn ::= (Const ( 10));;
        Callfun mm ''min'' [(V aa), (V nn)]
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.globals = [aa, nn, mm],
      program.procs = [min_decl, main_decl]
    \<rparr>"

export_code p in SML

(* The minimum of the array should be 1 and saved in global variable mm *)
value "execute_show [] p"

definition "minimum \<equiv> (
  shows_prog p ''''
)"

ML_val {*
  val str = @{code minimum} |> String.implode;
  writeln str;
  val os = TextIO.openOut "/home/gabriela/Documents/thesis/src/TestC/min_gen.c";
  TextIO.output (os, str);
  TextIO.flushOut os;
  TextIO.closeOut os;
*}

end
