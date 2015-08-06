theory Com
imports Exp
begin

section \<open>Commands\<close>

subsection \<open>Type definitions\<close>

text \<open>A function name is of type string.\<close>
type_synonym fname = string

subsection \<open>Commands definition\<close>

text \<open>The set of commands included in the semantics is:
  @{term SKIP} to represent an empty command.
  @{term Assignl} to represent an assignment to an address in memory.
  @{term Assign} to represent an assignment to a variable.
  @{term Seq} to represent sequential composition.
  @{term If} to represent an if-then-else command.
  @{term While} to represent a while loop.
  @{term Free} to represent a call to the free function in C.
  @{term Return} to represent a return from a function that returns a value.
  @{term Returnv} to represent a return form a procedure that returns void.
  @{term Callfunl} to represent a function call whose result value is stored in an address in memory.
  @{term Callfun} to represent a function call whose result value is stored in a variable.
  @{term Callfunv} to represent a procedure call that returns void.

  When a function returns a value this value must be stored in a variable or an address in memory.
\<close>

datatype
  com = SKIP
      | Assignl lexp exp       ("_ ::== _" [1000, 61] 61)
      | Assign  vname exp      ("_ ::= _" [1000, 61] 61)
      | Seq     com  com       ("_;;/ _"  [60, 61] 60)
      | If      exp com com    ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While   exp com        ("(WHILE _/ DO _)"  [0, 61] 61)
      | Free    lexp           ("FREE _" [0])
      | is_Return: Return exp  ("RETURN _" [0])
      | Returnv                ("RETURNV") (* Return for functions that return void *)
      | Callfunl lexp fname "exp list" ("_ ::== _ '(_')" [1000, 61] 61)
      | Callfun vname fname "exp list" ("_ ::= _ '(_')" [1000, 61] 61)
      | Callfunv fname "exp list" ("CALL _ '(_')" [1000, 61] 61) (* Call for functions that return void *)

term "''x'' ::= ''fun'' ([])"
term "(Derefl (V ''x'')) ::== ''fun'' ([])"

text \<open>A function declaration consists of the name (@{term "name ::fname"}) of the function,
  the formal parameters (@{term "params :: vname list"}) of the function, the local variables 
  (@{term "locals :: vname list"}) declared in the function and finally the body
  (@{term "body :: com"}) of the function.
\<close>
record fun_decl =
  name :: fname
  params :: "vname list"
  locals :: "vname list"
  body :: com

hide_const (open) name params locals body

text \<open>We define @{term valid_fun_decl} of type @{typeof valid_fun_decl}. A function declaration is
  valid iff the parameters and the locals have diferent names.\<close>
fun valid_fun_decl :: "fun_decl \<Rightarrow> bool" 
  where "valid_fun_decl fdecl \<longleftrightarrow> 
    distinct (fun_decl.params fdecl @ fun_decl.locals fdecl)"


text \<open>A @{term program} consists of the name of the program, the global variables in the program
  and the procedures declared in said program.\<close>
record program =
  name :: string
  globals :: "vname list"
  procs :: "fun_decl list"

hide_const (open) globals procs

text \<open>We define a procedure table of type @{typeof proc_table} it takes a function name and returns
  @{term None} if the procedure doesn't exist and @{term "Some fun_decl"} if the declaration exists\<close>
type_synonym proc_table = "fname \<rightharpoonup> fun_decl"

text \<open>We construct the procedure table for a program by taking the function declarations in the
  program and constructing a function of type @{typeof proc_table} with the names and declarations
  of the procedures.\<close>
definition proc_table_of :: "program \<Rightarrow> proc_table" where
  "proc_table_of p = map_of (map (\<lambda>fd. (fun_decl.name fd, fd)) (program.procs p))"

text \<open>We define a list containing the reserved keywords in C\<close>
definition reserved_keywords :: "vname list" where
  "reserved_keywords =
    [''auto'', ''break'', ''case'', ''char'', ''const'', ''continue'',
     ''default'', ''do'', ''double'', ''else'', ''enum'', ''extern'',
     ''float'', ''for'', ''goto'', ''if'', ''inline'', ''int'', ''long'',
     ''register'', ''restrict'', ''return'', ''short'', ''signed'', ''sizeof'',
     ''static'', ''struct'', ''switch'', ''typedef'', ''union'', ''unsigned'',
     ''void'', ''volatile'', ''while'', ''_Bool'', ''_Complex'', ''_Imaginary'']"

text \<open>We define a list containing the reserved keywords we will use for testing\<close>
definition test_keywords :: "vname list" where
  "test_keywords =
    [''__test_harness_num_tests'', ''__test_harness_passed'',
     ''__test_harness_failed'', ''__test_harness_discovered'']"


text \<open>We define a @{term collect_locals} function that collect the names of the local variables in
  all the procedures in the program.\<close>
fun collect_locals :: "fun_decl list \<Rightarrow> vname list" where
  "collect_locals [] = []"
| "collect_locals (p#ps) = (fun_decl.locals p) @ (collect_locals ps)"


text \<open>A program is considered valid if it complies with the following conditions:
  * The names for the global variables are different.
  * The names for the procedures in the program are different.
  * Every function declaration for every procedure in the program must be a valid.
  * The main procedure must be defined.
  * None of the variable names or procedure names in the program must be a reserved keyword from C
    or a reserved keyword for testing.
  * The global variables and the procedure names in a program can't be the same.
\<close>
definition valid_program :: "program \<Rightarrow> bool" 
  where "valid_program p \<equiv> 
      distinct (program.globals p)
    \<and> distinct (map fun_decl.name (program.procs p))
    \<and> (\<forall>fd\<in>set (program.procs p). valid_fun_decl fd)
    \<and> ( let
          pt = proc_table_of p
        in
         ''main'' \<in> dom pt
       \<and> fun_decl.params (the (pt ''main'')) = []
      )
    \<and> ( let
          prog_vars = set ((program.globals p) @ collect_locals (program.procs p));
          proc_names = set (map (fun_decl.name) (program.procs p))
        in
          (\<forall>name \<in> prog_vars. name \<notin> set (reserved_keywords @ test_keywords)) \<and>
          (\<forall>name \<in> proc_names. name \<notin> set (reserved_keywords @ test_keywords)) \<and>
          (\<forall>fname \<in> proc_names. (\<forall>vname \<in> set (program.globals p). fname \<noteq> vname))
      )"

(* I can't generate SML code for valid_program when using @{term dom} so I redefine it for code
   generation. *)
context begin

private lemma dom_pt_of_alt: "dom (proc_table_of p) = set (map fun_decl.name (program.procs p))"
  unfolding proc_table_of_def 
  apply (simp add: dom_map_of_conv_image_fst)
  apply force
  done

lemma valid_program_code[code]: "valid_program p \<longleftrightarrow>
      distinct (program.globals p)
    \<and> distinct (map fun_decl.name (program.procs p))
    \<and> (\<forall>fd\<in>set (program.procs p). valid_fun_decl fd)
    \<and> ''main'' \<in> set (map fun_decl.name (program.procs p))
    \<and> (let
          pt = proc_table_of p
       in
         fun_decl.params (the (pt ''main'')) = []
      )
    \<and> ( let
          prog_vars = set ((program.globals p) @ collect_locals (program.procs p));
          proc_names = set (map (fun_decl.name) (program.procs p))
        in
          (\<forall>name \<in> prog_vars. name \<notin> set (reserved_keywords @ test_keywords)) \<and>
          (\<forall>name \<in> proc_names. name \<notin> set (reserved_keywords @ test_keywords)) \<and>
          (\<forall>fname \<in> proc_names. (\<forall>vname \<in> set (program.globals p). fname \<noteq> vname))
      )"
  unfolding valid_program_def
  unfolding Let_def
  apply (subst dom_pt_of_alt)
  by simp

end

end

