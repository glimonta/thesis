section \<open>Programs\<close>
theory Program
imports Exp Type
begin

type_synonym fname = string -- \<open>Function name\<close>

text \<open>
  We cover a basic set of commands. 
  We have factored out some statements that are expressions in C99 to commands.
  This allows us to have expressions that never modify the state, which simplifies
  reasoning about sequence points, as all side-effects occur during execution of 
  a command.
\<close>

subsection \<open>Commands\<close>

datatype bcom = 
    Assign  exp exp                 -- \<open>Assignment\<close>
  | Malloc  exp ty exp              -- \<open>Memory allocation\<close>
  | Free    exp                     -- \<open>Memory deallocation\<close>
hide_const (open) Assign Malloc Free

datatype fcom = 
    Return exp                      -- \<open>Return with argument\<close>
  | Returnv                         -- \<open>Return without argument\<close>
  | Callfun exp fname "exp list"    -- \<open>Function call, assigning return value\<close>
  | Callfunv fname "exp list"       -- \<open>Function call, ignoring return value\<close>
hide_const (open) Return Returnv Callfun Callfunv

datatype com = 
    Skip                            -- \<open>Empty command that has no effect, and marks terminal state\<close>
  | Basic bcom                      -- \<open>Basic command, that has effect on current function scope only\<close>
  | Func fcom                       -- \<open>Function call or return command\<close>
  | Seq     com  com                -- \<open>Sequential composition of commands\<close>
  | If      exp com com             -- \<open>If-then-else command\<close>
  | While   exp com                 -- \<open>While loop\<close>

hide_const (open) Basic Func Seq If While Skip

abbreviation "com_Assign x y \<equiv> com.Basic (bcom.Assign x y)"
abbreviation "com_Malloc x y z \<equiv> com.Basic (bcom.Malloc x y z)"
abbreviation "com_Free x \<equiv> com.Basic (bcom.Free x)"

abbreviation "com_Return x \<equiv> com.Func (fcom.Return x)"
abbreviation "com_Returnv \<equiv> com.Func (fcom.Returnv)"
abbreviation "com_Callfun x y z \<equiv> com.Func (fcom.Callfun x y z)"
abbreviation "com_Callfunv x y \<equiv> com.Func (fcom.Callfunv x y)"

locale com_syntax = exp_syntax 
begin
  notation com.Skip      ("SKIP")
  notation com_Assign    ("_ := _" [100, 61] 61)
  notation com.Seq       ("_;;/ _"  [59, 60] 59)
  notation com.If        ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  notation com.While     ("(WHILE _/ DO _)"  [0, 61] 61)
  notation com_Malloc    ("_ := malloc _ [_]" [100,61,61] 61) 
  notation com_Free      ("free _" [100] 61)
  notation com_Return    ("return _" [61] 61)
  notation com_Returnv   ("return")
  notation com_Callfun   ("_ := _ ! _" [100, 1000,1000] 60)
  notation com_Callfunv  ("_ ! _" [1000] 60)

  term "* ($''x'' + I 3) := ''f''! [I 1 + $''x''];; $''y'':=''g''![]"
  term "($''x'') := ''fun''! []"
  term "* $''x'' := ''fun''! []"
end

text \<open>A function declaration consists of the name (@{term "name ::fname"}) of the function,
  the formal parameters (@{term "params :: vname list"}) of the function, the local variables 
  (@{term "locals :: vname list"}) declared in the function and finally the body
  (@{term "body :: com"}) of the function.
\<close>

type_synonym vdecl = "vname * ty"
subsection \<open>Functions\<close>
record fun_decl -- \<open>Function declaration\<close>
  =
  name :: fname           -- \<open>Name\<close>
  rtype :: "ty option"    -- \<open>Return type\<close>
  params :: "vdecl list"  -- \<open>Formal parameters\<close>
  locals :: "vdecl list"  -- \<open>Local variables\<close>
  body :: com             -- \<open>Function body\<close>  

hide_const (open) name params locals body rtype

subsection \<open>Structures\<close>
record struct_decl -- \<open>Structure declaration\<close>
=
  name :: sname           -- \<open>Structure name\<close>
  members :: "mdecl list" -- \<open>Member declarations\<close>
hide_const (open) name members

subsection \<open>Programs\<close>
record program  -- \<open>Program\<close>
=
  name :: string                -- \<open>Program name\<close>
  structs :: "struct_decl list" -- \<open>Structures\<close>
  globals :: "vdecl list"       -- \<open>Global variables\<close>
  functs :: "fun_decl list"      -- \<open>Functions\<close>

hide_const (open) name globals functs structs

subsection \<open>Miscellaneous\<close>
text \<open>We define a list containing the reserved keywords in C\<close>
definition reserved_keywords :: "string set" where
  "reserved_keywords =
    {''auto'', ''break'', ''case'', ''char'', ''const'', ''continue'',
     ''default'', ''do'', ''double'', ''else'', ''enum'', ''extern'',
     ''float'', ''for'', ''goto'', ''if'', ''inline'', ''int'', ''long'',
     ''register'', ''restrict'', ''return'', ''short'', ''signed'', ''sizeof'',
     ''static'', ''struct'', ''switch'', ''typedef'', ''union'', ''unsigned'',
     ''void'', ''volatile'', ''while'', ''_Bool'', ''_Complex'', ''_Imaginary''}"

text \<open>We define a list containing the reserved keywords we will use for testing\<close>
definition test_keywords :: "vname set" where
  "test_keywords =
    {''__test_harness_num_tests'', ''__test_harness_passed'',
     ''__test_harness_failed'', ''__test_harness_discovered''}"

definition "main_fname \<equiv> ''main''"
definition "malloc_fname \<equiv> ''__chloe_malloc''"
definition "free_fname \<equiv> ''free''"

text \<open>Reserved function names used by execution environment\<close>
(* FIXME/TODO: There are more! Documented in C99 Appendix B. Add them! *)
definition "reserved_fnames = {''malloc'', ''calloc'', ''free'', malloc_fname, free_fname}"

definition "keywords \<equiv> reserved_keywords \<union> test_keywords \<union> reserved_fnames"




definition mk_struct_map :: "program \<Rightarrow> struct_map" where
  "mk_struct_map p \<equiv> 
    map_of (map (\<lambda>sd. (struct_decl.name sd, struct_decl.members sd)) (program.structs p))"

definition mk_fun_map :: "program \<Rightarrow> fname \<rightharpoonup> fun_decl" where
  "mk_fun_map p \<equiv> 
    map_of (map (\<lambda>fd. (fun_decl.name fd,fd)) (program.functs p))"


end

