theory StrLength
imports "../SmallStep" Test
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
          pp ::= Plus (V pp) (Const ( 8)) (* Size of signed long *)
          );;
        Return (V ll)
    \<rparr>"

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
    \<lparr> program.globals = [aa, ll],
      program.procs = [create_array_decl, str_len_decl, main_decl]
    \<rparr>"

export_code p in SML

(* The length of the string should be 5 and be saved in global variable ll *)
value "execute_show [] p"

definition "strleng \<equiv> (
  shows_prog p ''''
)"

ML_val {*
  val str = @{code strleng} |> String.implode;
  writeln str;
  val os = TextIO.openOut "/home/gabriela/Documents/thesis/src/TestC/strlen_gen.c";
  TextIO.output (os, str);
  TextIO.flushOut os;
  TextIO.closeOut os;
*}

end
