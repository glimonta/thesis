theory Com
imports Exp Type
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
      | Free    exp            ("FREE _" [0])
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
  rtype :: "type option"
  params :: "vdecl list"
  locals :: "vdecl list"
  body :: com

abbreviation "fun_decl_param_names \<equiv> map snd o fun_decl.params"
abbreviation "fun_decl_local_names \<equiv> map snd o fun_decl.locals"

abbreviation "fun_decl_param_types \<equiv> map fst o fun_decl.params"
abbreviation "fun_decl_local_types \<equiv> map fst o fun_decl.locals"

hide_const (open) name params locals body rtype

text \<open>A structure declaration contains the name of the structure, and its (typed) fields\<close>
record struct_decl =
  name :: sname
  members :: "vdecl list"

hide_const (open) name members


text \<open>A @{term program} consists of the name of the program, the global variables in the program
  and the procedures declared in said program.\<close>
record program =
  name :: string
  globals :: "vdecl list"
  procs :: "fun_decl list"
  structs :: "struct_decl list"

hide_const (open) name globals procs structs

text \<open>We define a procedure table of type @{typeof proc_table} it takes a function name and returns
  @{term None} if the procedure doesn't exist and @{term "Some fun_decl"} if the declaration exists\<close>
type_synonym proc_table = "fname \<rightharpoonup> fun_decl"
type_synonym struct_table = "sname \<rightharpoonup> struct_decl"

text \<open>We construct the procedure table for a program by taking the function declarations in the
  program and constructing a function of type @{typeof proc_table} with the names and declarations
  of the procedures.\<close>
definition proc_table_of :: "program \<Rightarrow> proc_table" where
  "proc_table_of p = map_of (map (\<lambda>fd. (fun_decl.name fd, fd)) (program.procs p))"

definition struct_table_of :: "program \<Rightarrow> struct_table" where
  "struct_table_of p = map_of (map (\<lambda>sd. (struct_decl.name sd, sd)) (program.structs p))"


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

definition "is_keyword n \<equiv> n \<in> set reserved_keywords \<or> n \<in> set test_keywords"

text \<open>We define a @{term collect_locals} function that collect the names of the local variables in
  all the procedures in the program.\<close>
fun collect_locals :: "fun_decl list \<Rightarrow> vname list" where
  "collect_locals [] = []"
| "collect_locals (p#ps) = (map snd (fun_decl.locals p)) @ (collect_locals ps)"


fun snames_valid :: "sname set \<Rightarrow> type \<Rightarrow> bool" 
  -- \<open>Check that all used structure names are declared\<close>
where
  "snames_valid S (TNull) \<longleftrightarrow> True"
| "snames_valid S (TInt) \<longleftrightarrow> True"
| "snames_valid S (TPtr T) \<longleftrightarrow> snames_valid S T"
| "snames_valid S (TStruct n) \<longleftrightarrow> n\<in>S"

fun snames_complete :: "sname set \<Rightarrow> type \<Rightarrow> bool" 
  -- \<open>Check that all directly used struct types are completed\<close>
where
  "snames_complete C (TNull) \<longleftrightarrow> True"
| "snames_complete C (TInt) \<longleftrightarrow> True"
| "snames_complete C (TPtr T) \<longleftrightarrow> True"
| "snames_complete C (TStruct n) \<longleftrightarrow> n\<in>C"

fun valid_exp :: "sname set \<Rightarrow> exp \<Rightarrow> bool" and valid_lexp :: "sname set \<Rightarrow> lexp \<Rightarrow> bool" where
  "valid_exp S (Const _) \<longleftrightarrow> True"
| "valid_exp S Null \<longleftrightarrow> True"
| "valid_exp S (V _) \<longleftrightarrow> True"
| "valid_exp S (Plus e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Subst e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Minus e1) \<longleftrightarrow> valid_exp S e1"
| "valid_exp S (Div e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Mod e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Mult e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Less e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Not e1) \<longleftrightarrow> valid_exp S e1"
| "valid_exp S (And e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Or e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (Eq e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"
| "valid_exp S (New T e1) \<longleftrightarrow> snames_valid S T \<and> valid_exp S e1"
| "valid_exp S (Deref e1) \<longleftrightarrow> valid_exp S e1"
| "valid_exp S (Ref e1) \<longleftrightarrow> valid_lexp S e1"
| "valid_exp S (Index e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"

| "valid_lexp S (Derefl e1) \<longleftrightarrow> valid_exp S e1"
| "valid_lexp S (Indexl e1 e2) \<longleftrightarrow> valid_exp S e1 \<and> valid_exp S e2"


fun valid_com :: "sname set \<Rightarrow> com \<Rightarrow> bool" where
  "valid_com S SKIP \<longleftrightarrow> True"
| "valid_com S (Assignl le e) \<longleftrightarrow> valid_lexp S le \<and> valid_exp S e"
| "valid_com S (Assign x e) \<longleftrightarrow> valid_exp S e"
| "valid_com S (Seq c1 c2) \<longleftrightarrow> valid_com S c1 \<and> valid_com S c2"
| "valid_com S (If b c1 c2) \<longleftrightarrow> valid_exp S b \<and> valid_com S c1 \<and> valid_com S c2"
| "valid_com S (While b c1) \<longleftrightarrow> valid_exp S b \<and> valid_com S c1"
| "valid_com S (Free e) \<longleftrightarrow> valid_exp S e"
| "valid_com S (Return e) \<longleftrightarrow> valid_exp S e"
| "valid_com S (Returnv) \<longleftrightarrow> True"
| "valid_com S (Callfunl le _ args) \<longleftrightarrow> valid_lexp S le \<and> (\<forall>e\<in>set args. valid_exp S e)"
| "valid_com S (Callfun _ _ args) \<longleftrightarrow> (\<forall>e\<in>set args. valid_exp S e)"
| "valid_com S (Callfunv _ args) \<longleftrightarrow> (\<forall>e\<in>set args. valid_exp S e)"





definition valid_vdecl :: "sname set \<Rightarrow> vdecl \<Rightarrow> bool" where
  "valid_vdecl S \<equiv> \<lambda>(T,x). snames_valid S T \<and> \<not>is_keyword x"

definition valid_vdecl_list :: "sname set \<Rightarrow> vdecl list \<Rightarrow> bool" where
  "valid_vdecl_list S vds \<equiv> distinct (map snd vds) \<and> (\<forall>vd\<in>set vds. valid_vdecl S vd)"

text \<open>We define @{term valid_fun_decl} of type @{typeof valid_fun_decl}. A function declaration is
  valid iff the parameters and the locals have different names.\<close>
definition valid_fun_decl :: "sname set \<Rightarrow> fun_decl \<Rightarrow> bool" 
  where "valid_fun_decl S fdecl \<longleftrightarrow> 
    valid_vdecl_list S (fun_decl.params fdecl @ fun_decl.locals fdecl)
  \<and> (case fun_decl.rtype fdecl of None \<Rightarrow> True | Some T \<Rightarrow> snames_valid S T)  
  \<and> \<not>is_keyword (fun_decl.name fdecl)
  \<and> valid_com S (fun_decl.body fdecl)"

definition valid_struct_decl :: "sname set \<Rightarrow> struct_decl \<Rightarrow> bool" where
  "valid_struct_decl S sd \<equiv> 
    distinct (map snd (struct_decl.members sd))
  \<and> (\<forall>(T,n) \<in> set (struct_decl.members sd). snames_valid S T \<and> \<not>is_keyword n)  
  \<and> (\<not>is_keyword (struct_decl.name sd))
  "

definition check_complete_struct_decl :: "struct_decl \<Rightarrow> sname set \<rightharpoonup> sname set" where
  "check_complete_struct_decl sd C \<equiv> do {
    assert (\<forall>(T,_)\<in>set (struct_decl.members sd). snames_complete C T);
    Some (insert (struct_decl.name sd) C)
  }"

abbreviation "fold_option f l s \<equiv> fold (\<lambda>x s. Option.bind s (f x)) l (Some s)"

definition check_struct_decls_complete :: "struct_decl list \<Rightarrow> bool" where
  "check_struct_decls_complete sds \<equiv> fold_option check_complete_struct_decl sds {} \<noteq> None"


locale program_loc = 
  fixes p :: program 
begin  
  abbreviation "globals \<equiv> program.globals p"
  abbreviation "name \<equiv> program.name p"
  abbreviation "procs \<equiv> program.procs p"
  abbreviation "structs \<equiv> program.structs p"

  abbreviation "proc_table \<equiv> proc_table_of p"
  abbreviation "struct_table \<equiv> struct_table_of p"
  definition "main_decl \<equiv> the (proc_table ''main'')"

  abbreviation "proc_names \<equiv> dom proc_table"
  abbreviation "global_names \<equiv> set (map snd globals)"

  abbreviation struct_names :: "sname set" where
    "struct_names \<equiv> set (map struct_decl.name (program.structs p))"

end  



text \<open>A program is considered valid if it complies with the following conditions:
  * The names for the global variables are different.
  * The names for the procedures in the program are different.
  * Every function declaration for every procedure in the program must be a valid.
  * The main procedure must be defined.
  * None of the variable names or procedure names in the program must be a reserved keyword from C
    or a reserved keyword for testing.
  * The global variables and the procedure names in a program can't be the same.
  * Structure declarations are valid
\<close>

locale valid_program = program_loc +
  assumes global_distinct: "distinct (map snd globals @ map fun_decl.name procs)"
  assumes globals_valid: "valid_vdecl_list struct_names globals"
  assumes structs_distinct: "distinct (map struct_decl.name structs)"
  assumes structs_valid: "sd \<in> set structs \<Longrightarrow> valid_struct_decl struct_names sd"
  assumes structs_complete: "check_struct_decls_complete structs"
  assumes procs_valid: "fd\<in>set procs \<Longrightarrow> valid_fun_decl struct_names fd"
  assumes main_exists: "''main'' \<in> proc_names"
  assumes main_no_params[simp]: "fun_decl.params (main_decl) = []"
begin
  lemma valid_fun_declI: "proc_table f = Some fd \<Longrightarrow> valid_fun_decl struct_names fd"
    using procs_valid global_distinct 
    by (auto simp: proc_table_of_def dest!: map_of_SomeD)

  lemma valid_struct_declI: "struct_table f = Some sd \<Longrightarrow> valid_struct_decl struct_names sd"
    using structs_valid structs_distinct 
    by (auto simp: struct_table_of_def dest!: map_of_SomeD)

end

definition "valid_program_code p \<equiv> let
  S =  set (map struct_decl.name (program.structs p))
in
  distinct (map snd (program.globals p) @ map fun_decl.name (program.procs p))
\<and> distinct (map struct_decl.name (program.structs p))
\<and> (\<forall>fd\<in>set (program.procs p). valid_fun_decl S fd)
\<and> (\<forall>sd\<in>set (program.structs p). valid_struct_decl S sd)
\<and> check_struct_decls_complete (program.structs p)
\<and> (let 
    pt = proc_table_of p 
   in 
    case pt ''main'' of 
      Some fd \<Rightarrow> fun_decl.params fd = []
    | None \<Rightarrow> False
  )
\<and> (valid_vdecl_list S (program.globals p))
"

export_code valid_program_code checking SML

lemma valid_program_code[code]: "valid_program p = valid_program_code p"
proof
  assume "valid_program p"
  then interpret valid_program p .

  show "valid_program_code p"
    unfolding valid_program_code_def
    using global_distinct structs_distinct procs_valid main_exists main_no_params globals_valid
      structs_valid structs_complete
    by (auto simp: main_decl_def)

next
  interpret program_loc p .
  assume "valid_program_code p"
  thus "valid_program p"
    apply unfold_locales
    unfolding valid_program_code_def
    by (auto simp: main_decl_def Let_def split: option.splits)
qed

end

