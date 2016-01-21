section \<open>Pretty printing of Programs\<close>
theory Pretty_Program
imports Program "../Semantics/Arith" "../Lib/Show/Show_Instances" "../Typing/Type_Checker"
begin

subsection \<open>Integer Type\<close>
  definition "int_width_str \<equiv> show int_width"

  definition "int_type \<equiv> ''int'' @ int_width_str @ ''_t''"

  definition "int_type_min_bound_name \<equiv> ''INT'' @ int_width_str @ ''_MIN''"
  definition "int_type_max_bound_name \<equiv> ''INT'' @ int_width_str @ ''_MAX''"

  definition "size_type \<equiv> ''size_t''"
  definition "ptrdiff_type \<equiv> ''ptrdiff_t''"

  definition "ptrdiff_type_min_bound_name \<equiv> ''PTRDIFF_MIN''"
  definition "ptrdiff_type_max_bound_name \<equiv> ''PTRDIFF_MAX''"
  definition "size_type_max_bound_name \<equiv> ''SIZE_MAX''"


text \<open>We define an assert that must be made in every program we generate C code for.
  This semantics is based on 64bit integers, and therefore the only way that we can guarantee
  that the code generated with this pretty printer will remain correct once translated to C
  is to make sure that the architecture in which the program is executed the type bounds are
  defined.\<close>
  definition "preproc_assert_defined a \<equiv> ''#ifndef '' @ a @ ''\<newline>  #error (\"Macro ''@a@'' undefined\")\<newline>#endif\<newline>''"

text \<open>We define an assert that must be made in every program we generate C code for.
  This semantics is based on 64bit integers, and therefore the only way that we can guarantee
  that the code generated with this pretty printer will remain correct once translated to C
  is to make sure that the architecture in which the program is executed the type bounds are
  equal to the type bounds we define here, namely @{term INT_MAX} and @{term INT_MIN}\<close>
  definition "preproc_assert_eq a b reason \<equiv> 
    ''/* '' @ reason @ '' */\<newline>''
  @ ''#if ( '' @ a @ '' != '' @ b  @ '' )\<newline>'' 
  @ '' #error (\"Assertion '' @ a @ '' == '' @ b @ '' failed\")\<newline>''
  @ ''#endif\<newline>''"

  definition "preproc_assert_leq a b reason \<equiv> 
    ''/* '' @ reason @ '' */\<newline>''
  @ ''#if ( '' @ a @ '' > '' @ b  @ '' )\<newline>'' 
  @ '' #error (\"Assertion '' @ a @ '' <= '' @ b @ '' failed\")\<newline>''
  @ ''#endif\<newline>''"

text \<open>This is the generated code for checking that the architecture in which the program will
  be compiled and executed complies with the assumptions made in this semantics.
  Note that this check is not necessary if the C compiler complies to C99, as the
  used type, @{text intN_t} is required to have exactly those bounds.
\<close>
  definition integer_bounds_check :: string where
    "integer_bounds_check \<equiv> 
      preproc_assert_defined int_type_min_bound_name
    @ preproc_assert_defined int_type_max_bound_name
    @ preproc_assert_defined ptrdiff_type_max_bound_name
    @ preproc_assert_defined ptrdiff_type_min_bound_name
    @ preproc_assert_defined size_type_max_bound_name

    @ preproc_assert_eq (int_type_min_bound_name @ '' + 1'') (show (INT_MIN + 1))
        ( ''Check that minimum integer value coincides with the one in formal semantics\<newline>''
        @ ''Note: This also ensures that the implementation uses 2's complement integer representation\<newline>''
        @ ''TODO: Ugly workaround against the absolute value of INT_MIN\<newline>'' 
        @ ''exceeding INT_MAX of the preprocessor, and the preprocessor interprets\<newline>''
        @ ''-number as -(number), and gives a warning it cannot represent number'')
    @ preproc_assert_eq int_type_max_bound_name (show INT_MAX)
        ''Check that maximum integer value coincides with the one in formal semantics''
    @ preproc_assert_eq ptrdiff_type_min_bound_name int_type_min_bound_name
      ''Check that ptrdiff_t and integer type coincide (min)''
    @ preproc_assert_eq ptrdiff_type_max_bound_name int_type_max_bound_name
      ''Check that ptrdiff_t and integer type coincide (max)''
    @ preproc_assert_leq int_type_max_bound_name size_type_max_bound_name 
        ( ''Check that integer type is not bigger than size type,\<newline>''
        @ '' so we can safely cast from integer to size_t'')
    "




subsection \<open>Pretty printing of binary and unary operations\<close>

text \<open>A binary operation is pretty printed in an infix way:
  (<operand_1> <operator> <operand_2>)

  We show parenthesis around the operation to ensure correct precedence in the operations.
\<close>
  abbreviation "shows_binop s1 opr s2 \<equiv> 
    shows_paren s1 o shows_space o shows opr o shows_space o shows_paren s2"

text \<open>An unary operation is pretty printed in the following way:
  <operator> (<operand>)

  We show parenthesis around the operator to ensure correct precedence in the operations.
\<close>
  abbreviation "shows_unop opr s2 \<equiv> 
    shows opr o shows_space o shows_paren s2"

subsection \<open>Pretty printing of expressions\<close>

text \<open>Another C99 joke: A negative number is parsed as two literals:
  Unary minus and positive number ... causing trouble if the number is
  int_min, as the absolute value is not representable within the int type.

  This function works around this issue by replacing int_min by the
  corresponding macro.
  \<close>
  definition shows_int_const :: "int \<Rightarrow> shows" where
    "shows_int_const i \<equiv> 
      if i<INT_MIN \<or> i>INT_MAX then Code.abort (STR ''Show-constant: too big'') (\<lambda>_. shows '''')
      else if i=INT_MIN then shows int_type_min_bound_name 
      else shows i"

text \<open>From the previous definitions on pretty printing the definition of @{term shows_exp}
  and @{term shows_lexp} should be straightforward.\<close>

  primrec shows_op0 :: "op0 \<Rightarrow> shows" where
    "shows_op0 (op0.Const i) = shows_int_const i"
  | "shows_op0 (op0.Null) = shows ''0''"  
  | "shows_op0 (op0.Var x) = shows x"  

  primrec shows_op1 :: "op1 \<Rightarrow> shows \<Rightarrow> shows" where
    "shows_op1 op1.UMinus x = shows_unop ''-'' x"
  | "shows_op1 op1.Not x = shows_unop ''!'' x"
  | "shows_op1 op1.BNot x = shows_unop ''~'' x"
  | "shows_op1 op1.Deref x = shows_unop ''*'' x"
  | "shows_op1 op1.Ref x = shows_unop ''&'' x"
  | "shows_op1 (op1.Memb name) x = shows_paren x o shows ''.'' o shows name"
  | "shows_op1 (op1.Membp name) x = shows_paren x o shows ''->'' o shows name"
  
  primrec shows_op2 :: "op2 \<Rightarrow> shows \<Rightarrow> shows \<Rightarrow> shows" where
    "shows_op2 op2.Plus x y = shows_binop x ''+'' y"
  | "shows_op2 op2.Minus x y = shows_binop x ''-'' y"

  | "shows_op2 op2.Mult x y = shows_binop x ''*'' y"
  | "shows_op2 op2.Div x y = shows_binop x ''/'' y"
  | "shows_op2 op2.Mod x y = shows_binop x ''%'' y"

  | "shows_op2 op2.Less x y = shows_binop x ''<'' y"
  | "shows_op2 op2.Leq x y = shows_binop x ''<='' y"
  | "shows_op2 op2.Eq x y = shows_binop x ''=='' y"

  | "shows_op2 op2.And x y = shows_binop x ''&&'' y"
  | "shows_op2 op2.Or x y = shows_binop x ''||'' y"

  | "shows_op2 op2.BAnd x y = shows_binop x ''&'' y"
  | "shows_op2 op2.BOr x y = shows_binop x ''|'' y"
  | "shows_op2 op2.BXor x y = shows_binop x ''^'' y"

  | "shows_op2 op2.Index x y = shows_paren x o shows CHR ''['' o y o shows CHR '']''"
  
  primrec shows_exp :: "exp \<Rightarrow> shows" where
    "shows_exp (exp.E0 f) = shows_op0 f"
  | "shows_exp (exp.E1 f e) = shows_op1 f (shows_exp e)"
  | "shows_exp (exp.E2 f e1 e2) = shows_op2 f (shows_exp e1) (shows_exp e2)"

subsection \<open>Pretty-Printing of types\<close>

definition "shows_struct_type (sname::sname) \<equiv> shows ''struct '' o shows sname"

definition "shows_ptr_to s \<equiv> shows_paren (shows CHR ''*'' o s)"  
definition "shows_array_of n s \<equiv> shows_paren (s o shows CHR ''['' o shows n o shows CHR '']'')"  

subsubsection \<open>Declarations\<close>
text \<open>The right-left rule determines how types are printed. \<close>
(* TODO: Regression tests against cdecl! *)
primrec shows_decl_aux :: "shows \<Rightarrow> ty \<Rightarrow> shows" where
  "shows_decl_aux s (ty.Null) = shows ''void'' o shows CHR '' '' o shows_ptr_to s"
| "shows_decl_aux s (ty.I) = shows int_type o shows CHR '' '' o s"
| "shows_decl_aux s (ty.Ptr ty) = shows_decl_aux (shows_ptr_to s) ty"
| "shows_decl_aux s (ty.Array n ty) = shows_decl_aux (shows_array_of n s) ty"
| "shows_decl_aux s (ty.StructPtr name) = 
    shows_struct_type name o shows CHR '' '' o shows_ptr_to s"
| "shows_decl_aux s (ty.Struct name _) = 
    shows_struct_type name o shows CHR '' '' o s"

definition shows_decl :: "vname \<times> ty \<Rightarrow> shows" where
  "shows_decl \<equiv> \<lambda>(name,ty). shows_decl_aux (shows name) ty"

abbreviation "shows_ty ty \<equiv> shows_decl ('''',ty)"

subsection \<open>Pretty printing of commands\<close>

text \<open>First of all we need a way of printing indented commands to facilitate the
  reading of the generated code.

  @{term indent} will print the indentation at the beginning, the command and finally a new line
  character.
  @{term indent_basic} will print the indentation at the beginning, the command, a semicolon and
  finally a new line character.
\<close>
  abbreviation "indent ind s \<equiv> shows (replicate (ind*2) CHR '' '') o s o shows_nl"
  abbreviation "indent_basic ind s \<equiv> shows (replicate (ind*2) CHR '' '') o s o shows '';'' o shows_nl"

text \<open>@{term shows_fun_call} will print a function call in the following way:
  <function_name> ([<argument_0>, ... ,<argument_n>])

  The brackets indicate that the arguments are optional, we can pretty print a function call
  without arguments.
\<close>
  definition "shows_fun_call fname args \<equiv> 
    shows fname o shows_paren (shows_sep shows_exp (shows '', '') args)"

definition shows_cast :: "ty \<Rightarrow> shows \<Rightarrow> shows" where
  "shows_cast ty s \<equiv> shows_paren (shows_decl ('''',ty)) o shows_paren s"

definition shows_malloc :: "exp \<Rightarrow> ty \<Rightarrow> exp \<Rightarrow> shows" where
  "shows_malloc e1 ty e2 \<equiv> do {
    let base_size = shows ''sizeof'' o shows_paren (shows_decl ('''', ty));
    let mult = shows_exp e2;
    let rhs = shows malloc_fname o shows_paren (base_size o shows '', '' o mult);
    let rhs = shows_cast (ty.Ptr ty) rhs;
    shows_binop (shows_exp e1) ''='' rhs
  }"

primrec shows_bcom_aux :: "bcom \<Rightarrow> shows" where
  "shows_bcom_aux (bcom.Assign e1 e2) = shows_binop (shows_exp e1) ''='' (shows_exp e2)"
| "shows_bcom_aux (bcom.Malloc e1 ty e2) = shows_malloc e1 ty e2"
| "shows_bcom_aux (bcom.Free e) = shows_fun_call free_fname [e]"

definition shows_bcom :: "nat \<Rightarrow> bcom \<Rightarrow> shows" where 
  "shows_bcom ind c \<equiv> indent_basic ind (shows_bcom_aux c)"

primrec shows_fcom_aux :: "fcom \<Rightarrow> shows" where
  "shows_fcom_aux (fcom.Return e) = shows ''return'' o shows_paren (shows_exp e)"
| "shows_fcom_aux (fcom.Returnv) = shows ''return''"
| "shows_fcom_aux (fcom.Callfun e f args) = shows_binop (shows_exp e) ''='' (shows_fun_call f args)"
| "shows_fcom_aux (fcom.Callfunv f args) = shows_fun_call f args"

definition shows_fcom :: "nat \<Rightarrow> fcom \<Rightarrow> shows" where 
  "shows_fcom ind c \<equiv> indent_basic ind (shows_fcom_aux c)"

fun shows_com :: "nat \<Rightarrow> com \<Rightarrow> shows" where
  "shows_com ind com.Skip = shows ''''"
| "shows_com ind (com.Basic c) = shows_bcom ind c"
| "shows_com ind (com.Func c) = shows_fcom ind c"
| "shows_com ind (com.Seq c1 c2) = shows_com ind c1 o shows_com ind c2"
| "shows_com ind (com.If e c1 com.Skip) = 
    indent ind (shows ''if '' o shows_paren (shows_exp e) o shows '' {'' ) o
      shows_com (ind + 1) c1 o
    indent ind (shows ''}'')"
| "shows_com ind (com.If e c1 c2) = 
    indent ind (shows ''if '' o shows_paren (shows_exp e) o shows '' {'' ) o
      shows_com (ind + 1) c1 o
    indent ind (shows ''} else {'' ) o
      shows_com (ind + 1) c2 o
    indent ind (shows ''}'' )"
| "shows_com ind (com.While e c) = 
    indent ind (shows ''while '' o shows_paren (shows_exp e) o shows '' {'' ) o
      shows_com (ind + 1) c o
    indent ind (shows ''}'' )"

subsection \<open>Structure declarations\<close>
definition shows_struct_fwd_decl :: "struct_decl \<Rightarrow> shows" where
  "shows_struct_fwd_decl sd \<equiv> 
    shows ''struct '' o shows (struct_decl.name sd) o shows '';'' o shows_nl"

definition shows_struct_decl :: "struct_decl \<Rightarrow> shows" where
  "shows_struct_decl sd \<equiv> 
    shows ''struct '' o shows (struct_decl.name sd) o shows '' {'' o shows_nl o
      shows_sep (indent_basic 1 o shows_decl) id (struct_decl.members sd) o
    shows ''};'' o shows_nl"

subsection \<open>Global variables\<close>

definition shows_globals :: "vdecl list \<Rightarrow> shows" -- \<open>Show global variable declarations\<close>
(* TODO: Initializers *)
where
  "shows_globals vds \<equiv> shows_sep (indent_basic 1 o shows_decl) id vds"

subsection \<open>Function declarations\<close>

definition shows_arg :: "vdecl \<Rightarrow> shows" -- \<open>Show function argument\<close>
where
  "shows_arg \<equiv> shows_decl"   

definition shows_local :: "vdecl \<Rightarrow> shows" -- \<open>Show local variable declaration\<close>
(* TODO: Initializers *)
where
  "shows_local vd \<equiv> indent_basic 1 (shows_decl vd)"

definition shows_fun_prototype :: "fun_decl \<Rightarrow> shows" where
  "shows_fun_prototype fd \<equiv> do {
    let arglist = shows_paren ( shows_sep shows_arg (shows '', '') (fun_decl.params fd));
    let f = shows (fun_decl.name fd) o shows_space o arglist;
    case fun_decl.rtype fd of
      None \<Rightarrow> shows ''void '' o f
    | Some ty \<Rightarrow> shows_decl_aux f ty  
  }"


text\<open> A function declaration is pretty printed by printing the return type, the name of the
  function, the arguments separated by commas using @{term shows_arg} and then enclosed by
  brackets the declaration of the local variables using @{term shows_local} and finally
  the body of the function is pretty printed using @{term shows_com}.\<close>

definition shows_fun_fwd_decl :: "fun_decl \<Rightarrow> shows" where
  "shows_fun_fwd_decl fdecl \<equiv> shows_fun_prototype fdecl o shows '';'' o shows_nl"

definition shows_fun_decl :: "fun_decl \<Rightarrow> shows" where
  "shows_fun_decl fdecl \<equiv> 
    shows_fun_prototype fdecl o
        shows '' {'' o shows_nl o 
          shows_sep shows_local id (fun_decl.locals fdecl) o
          shows_com 1 (fun_decl.body fdecl) o
        shows ''}'' o shows_nl"


subsection \<open>Pretty printing of a program\<close>

text \<open>A program is pretty printing by first pretty printing the names of the standard libraries
  needed by the program:
  * stdlib.h
  * stdio.h
  * limits.h -- Here the max and min bounds for our type are defined
  * stdint.h -- For intptr_t type
  * ../test_harness.h -- Contains a series of macros used for regression testing
  * ../malloc_lib.h -- Contains the macro used for malloc calls

  followed by the @{term integer_bounds_check}, the global declarations, namely global variables
  and procedures (including main).
\<close>

  definition shows_prog :: "program \<Rightarrow> shows" where
    "shows_prog p \<equiv> 
      shows ''#include <stdlib.h>'' o
      shows_nl o
      shows ''#include <stdio.h>'' o
      shows_nl o
      shows ''#include <limits.h>'' o
      shows_nl o
      shows ''#include <stdint.h>'' o
      shows_nl o
      shows ''#include \"../test_harness.h\"'' o
      shows_nl o
      shows ''#include \"../malloc_lib.h\"'' o
      shows_nl o
      shows integer_bounds_check o
      shows_nl o shows_nl o

      shows_sep shows_struct_fwd_decl shows_nl (program.structs p) o
      shows_nl o
      shows_sep shows_struct_decl shows_nl (program.structs p) o
      shows_nl o
      shows_globals (program.globals p) o
      shows_nl o
      shows_sep shows_fun_fwd_decl shows_nl (program.functs p) o
      shows_nl o
      shows_sep shows_fun_decl shows_nl (program.functs p)"

subsection \<open>Exporting C code\<close>

(* TODO: Move *)
fun e2o :: "('a,'e) error \<Rightarrow> 'a option" where
  "e2o (return x) = Some x"
| "e2o _ = None"  

definition prepare_export' :: "program \<Rightarrow> string ck" where
  "prepare_export' p \<equiv> do {
    wt_program p;
    return (shows_prog p '''')
  }"

definition "prepare_export p \<equiv> e2o (prepare_export' p)"

export_code prepare_export in SML module_name Exporter

text \<open>We define a function in ML code that takes the code we want to generate C code for,
  the relative path in which we want to store our generated C program, a name for the program
  and a theory where we defined the program it will write the string generated by the pretty
  printer in that file.
  If either the relative path or the name are left blank the output will be printed to
  the Isabelle output view.
\<close>
ML \<open>
  exception Failed_Execution


  fun export_c_code (SOME code) rel_path name thy =
    let 
      val str = code |> String.implode;
    in
      if rel_path="" orelse name="" then
        (writeln str; thy)
      else let  
        val base_path = Resources.master_directory thy
        val rel_path = Path.explode rel_path
        val name_path = Path.basic name |> Path.ext "c"
      
        val abs_path = Path.appends [base_path, rel_path, name_path]
        val abs_path = Path.implode abs_path
     
        val _ = writeln ("Writing to file " ^ abs_path)
 
        val os = TextIO.openOut abs_path;
        val _ = TextIO.output (os, str);
        val _ = TextIO.flushOut os;
        val _ = TextIO.closeOut os;
        in thy end  
      end
  | export_c_code NONE _ _ thy = 
      (error "Invalid program, no code is generated."; thy)

  fun expect_failed_export (SOME _) = error "Expected failed export"
    | expect_failed_export NONE = ()
\<close>

end
