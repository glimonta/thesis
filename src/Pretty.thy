theory Pretty
imports Eval "Show/Show_Instances"
begin

section \<open>Pretty Printer\<close>

subsection \<open>Architecture checks\<close>

text \<open>Since there's no type information in our semantics and we keep a difference between
  pointers and integer values, when doing the translation to C code we're going to use the
  type @{term intptr_t} that can store integer **and** pointer values.\<close>
  definition "dflt_type \<equiv> ''intptr_t''" -- \<open>Important: Must match @{term int_width} !\<close>
  definition "dflt_type_bound_name \<equiv> ''INTPTR''"

  definition "dflt_type_min_bound_name \<equiv> dflt_type_bound_name @ ''_MIN''"
  definition "dflt_type_max_bound_name \<equiv> dflt_type_bound_name @ ''_MAX''"

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
  definition "preproc_assert_eq a b \<equiv> ''#if ( '' @ a @ '' != '' @ b 
    @ '' )\<newline>  #error (\"Assertion '' @ a @ '' == '' @ b @ '' failed\")\<newline>#endif\<newline>''"

text \<open>This is the generated code for checking that the architecture in which the program will
  be compiled and executed complies with the assumptions made in this semantics.
\<close>
  definition integer_bounds_check :: string where
    "integer_bounds_check \<equiv> 
      preproc_assert_defined dflt_type_min_bound_name
    @ preproc_assert_defined dflt_type_max_bound_name
    @ preproc_assert_eq (dflt_type_min_bound_name @ '' + 1'') (show (INT_MIN + 1))
      (* TODO: Ugly workaround against the absolute value of INT_MIN 
        exceeding INT_MAX of the preprocessor, and the preprocessor interprets
        -number as -(number), and gives a warning it cannot represent number *)
    @ preproc_assert_eq dflt_type_max_bound_name (show INT_MAX)"

subsection \<open>Pretty printing of words\<close>

text \<open> We make a new instance of shows for the type @{term word}, in order to be able to
  pretty print values of this type.\<close>
  instantiation word :: (len)"show" begin
    definition "shows_prec p w \<equiv> shows_prec p (sint w)"

    definition "shows_list (l::'a word list) \<equiv> showsp_list shows_prec 0 l"

    instance
      apply default
      unfolding shows_prec_word_def[abs_def] shows_list_word_def
      apply (simp_all add: show_law_simps)
      done
  end    

subsection \<open>Pretty printing of values\<close>

text \<open> We make a new instance of shows for the type @{term val}, in order to be able to
  pretty print values of this type.\<close>
  instantiation val :: "show" begin
    definition shows_prec_val where
      "shows_prec_val p v \<equiv> case v of 
        NullVal \<Rightarrow> shows ''null''
      | (I w) \<Rightarrow> shows_prec p w  
      | (A (base,ofs)) \<Rightarrow> 
        shows CHR ''*'' o shows base o shows CHR ''['' o shows ofs o shows CHR '']''
      "

    definition "shows_list (l::val list) \<equiv> showsp_list shows_prec 0 l"

    instance
      apply default
      unfolding shows_prec_val_def[abs_def] shows_list_val_def 
      apply (simp_all add: show_law_simps split: val.splits)
      done

  end    

subsection \<open>Pretty printing of return locations\<close>

text \<open> We make a new instance of shows for the type @{term return_loc}, in order to be able to
  pretty print values of this type.\<close>
  instantiation return_loc :: "show" begin
    definition shows_prec_return_loc where
      "shows_prec_return_loc (p::nat) v \<equiv> case v of 
        Ar addr \<Rightarrow> shows (A addr)
      | (Vr x) \<Rightarrow> shows x  
      | Invalid \<Rightarrow> shows ''<invalid>''"

    definition "shows_list (l::return_loc list) \<equiv> showsp_list shows_prec 0 l"

    instance
      apply default
      unfolding shows_prec_return_loc_def[abs_def] shows_list_return_loc_def 
      apply (simp_all add: show_law_simps split: return_loc.splits)
      done

  end    

subsection \<open>Pretty printing of @{term "val option"}\<close>

text \<open>A @{term "val option"} means uninitialized if it is @{term None}, and initialized with
  value v it is @{term "Some v"}. If it's @{term None} we pretty print a @{term "''?''"} meaning
  uninitialized.
\<close>
  fun showsp_val_option :: "val option showsp" where
    "showsp_val_option _ None = shows ''?''"
  | "showsp_val_option _ (Some v) = shows v"

subsection \<open>Pretty printing of valuations\<close>

text \<open>Given a list of variable names the valuation will be printed with the following format:
  [<vname_0> = <value_0>, <vname_1> = <value_1>, ... , <vname_n> = <value_n>]
\<close>
  definition shows_valuation :: "vname list \<Rightarrow> valuation \<Rightarrow> shows" where 
    "shows_valuation vnames val \<equiv> let
      shows_pair = (\<lambda>(x,v). shows x o shows '' = '' o showsp_val_option 0 v);
      pairs = map (\<lambda>(x,Some v) \<Rightarrow> (x,v)) (filter (\<lambda>(_,v). v\<noteq>None) (map (\<lambda>x. (x, val x)) vnames))
    in
      showsp_list (\<lambda>_. shows_pair) 0 pairs
      "

subsection \<open>Pretty printing of memory\<close>

text \<open>A memory block has the type @{term "val option list option"} if this list is @{term None}
  then the memory is free and we pretty print @{term "''<free>''"}, and if it's there we pretty
  print the value list.
\<close>
  fun showsp_block :: "val option list option showsp" where
    "showsp_block _ None = shows ''<free>''"
  | "showsp_block _ (Some l) = showsp_list showsp_val_option 0 l"  

text \<open>The memory is indexed by an @{term "A (base, ofs)"} in order to print a block we will
  use the following format:

  <block_number> : <block_content>

\<close>
  fun showsp_block_at :: "(nat \<times> val option list option) showsp" where
    "showsp_block_at _ (base, block) = shows base o shows '': '' o showsp_block 0 block"

text \<open>Finally we show every block of the memory following the previous format defined by
  @{term showsp_block_at} separated by new line characters.
\<close>
  definition showsp_mem :: "mem showsp" where
    "showsp_mem _ m \<equiv> shows_sep (showsp_block_at 0) shows_nl (enumerate 0 m)"

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

subsection \<open>Pretty printing of casts\<close>

text \<open>In our semantics we didn't define any type information. Therefore every variable in the
  generated C program will be of type @{term intptr_t}.

  Since we're working with pointers and integer values, we must make the explicit cast between
  these two types in our generated program.
  When an address value is needed we add the cast:

  (<type> *) <expression>

  When we need an integer value we add the cast:

  (<type>) <expression>
\<close>

  definition shows_cast_to_pointer :: "shows \<Rightarrow> shows" where
    "shows_cast_to_pointer s \<equiv> shows_paren ( shows dflt_type o shows ''*'') o s "

  definition shows_cast_to_dflt_type :: "shows \<Rightarrow> shows" where
    "shows_cast_to_dflt_type s \<equiv> shows_paren ( shows dflt_type ) o s "

subsection \<open>Pretty printing of expressions\<close>

text \<open>From the previous definitions on pretty printing the definition of @{term shows_exp}
  and @{term shows_lexp} should be straightforward.\<close>
  fun 
      shows_exp :: "exp \<Rightarrow> shows" 
  and shows_lexp :: "lexp \<Rightarrow> shows"
    where
    "shows_exp (Const int_val) = shows int_val"
  | "shows_exp (Null) = shows_cast_to_pointer (shows ''0'')"
  | "shows_exp (V x) = shows x"
  | "shows_exp (Plus e1 e2) = shows_binop (shows_exp e1) ''+'' (shows_exp e2)"
  | "shows_exp (Subst e1 e2) = shows_binop (shows_exp e1) ''-'' (shows_exp e2)"
  | "shows_exp (Minus e) = shows_unop ''-'' (shows_exp e)"
  | "shows_exp (Div e1 e2) = shows_binop (shows_exp e1) ''/'' (shows_exp e2)"
  | "shows_exp (Mod e1 e2) = shows_binop (shows_exp e1) ''%'' (shows_exp e2)"
  | "shows_exp (Mult e1 e2) = shows_binop (shows_exp e1) ''*'' (shows_exp e2)"
  | "shows_exp (Less e1 e2) = shows_binop (shows_exp e1) ''<'' (shows_exp e2)"
  | "shows_exp (Not e) = shows_unop ''!'' (shows_exp e)"
  | "shows_exp (And e1 e2) = shows_binop (shows_exp e1) ''&&'' (shows_exp e2)"
  | "shows_exp (Or e1 e2) = shows_binop (shows_exp e1) ''||'' (shows_exp e2)"
  | "shows_exp (Eq e1 e2) = shows_binop (shows_exp e1) ''=='' (shows_exp e2)"
  | "shows_exp (New e) = shows ''__MALLOC(sizeof('' o shows dflt_type o shows '') * '' o shows_paren (shows_exp e) o shows '')''"
  | "shows_exp (Deref e) = shows ''*'' o shows_paren (shows_cast_to_pointer (shows_exp e))"
  | "shows_exp (Ref e) = shows_cast_to_pointer (shows_unop ''&'' (shows_lexp e))"
  | "shows_exp (Index e1 e2) = shows_paren (shows_cast_to_pointer (shows_exp e1)) o shows CHR ''['' o shows_exp e2 o shows CHR '']''"
  | "shows_lexp (Derefl exp) = shows_paren (shows ''*'' o  shows_paren (shows_cast_to_pointer (shows_exp exp)))"
  | "shows_lexp (Indexl e1 e2) = shows_paren (shows_cast_to_pointer (shows_exp e1)) o shows CHR ''['' o shows_exp e2 o shows CHR '']''"


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

text \<open>From the previous definitions on pretty printing the definition of @{term shows_com}
  should be straightforward. It is done following C syntax.\<close>
  fun shows_com :: "nat \<Rightarrow> com \<Rightarrow> shows" where
    "shows_com ind SKIP = shows ''''"
  | "shows_com ind (Assignl x e) = indent_basic ind ( shows_binop (shows_lexp x) ''='' (shows_exp e))"  
  | "shows_com ind (Assign x e) = indent_basic ind ( shows x o shows '' = '' o shows_paren (shows_exp e))"
  | "shows_com ind (Seq c1 c2) = shows_com ind c1 o shows_com ind c2"
  | "shows_com ind (If e c1 SKIP) = 
      indent ind (shows ''if '' o shows_paren (shows_exp e) o shows '' {'' ) o
        shows_com (ind + 1) c1 o
      indent ind (shows ''}'')"
  | "shows_com ind (If e c1 c2) = 
      indent ind (shows ''if '' o shows_paren (shows_exp e) o shows '' {'' ) o
        shows_com (ind + 1) c1 o
      indent ind (shows ''} else {'' ) o
        shows_com (ind + 1) c2 o
      indent ind (shows ''}'' )"
  | "shows_com ind (While e c) = 
      indent ind (shows ''while '' o shows_paren (shows_exp e) o shows '' {'' ) o
        shows_com (ind + 1) c o
      indent ind (shows ''}'' )"
  | "shows_com ind (Free x) =
      indent_basic ind ( shows ''free'' o shows_paren (shows ''&'' o (shows_paren (shows_lexp x))))"
  | "shows_com ind (Return e) = indent_basic ind ( shows ''return'' o shows_paren (shows_exp e) )"
  | "shows_com ind (Returnv) = indent_basic ind ( shows ''return'' )"
  | "shows_com ind (Callfunl x f args) = 
      indent_basic ind (shows_binop (shows_lexp x) ''='' (shows_fun_call f args))"
  | "shows_com ind (Callfun x f args) = 
      indent_basic ind (shows_binop (shows x) ''='' (shows_fun_call f args))"
  | "shows_com ind (Callfunv f args) = 
      indent_basic ind ((shows_fun_call f args))"

subsection \<open>Pretty printing of function declarations\<close>

text \<open>Pretty printing of arguments of a function declaration are pretty printed as follows:
  <type> <argument_name>
\<close>
  definition shows_arg :: "string \<Rightarrow> shows" where
    "shows_arg s \<equiv> shows dflt_type o shows_space o shows s"

text \<open>A declaration of a local variable in a function is done with indentation = 1 and is
  pretty printed as follows:

  <type> <argument_name>;
\<close>
  definition shows_local :: "string \<Rightarrow> shows" where
    "shows_local s \<equiv> indent_basic 1 (shows dflt_type o shows_space o shows s)"

text\<open> A function declaration is pretty printed by printing the return type, the name of the
  function, the arguments separated by commas using @{term shows_arg} and then enclosed by
  brackets the declaration of the local variables using @{term shows_local} and finally
  the body of the function is pretty printed using @{term shows_com}.\<close>
  definition shows_fun_decl :: "fun_decl \<Rightarrow> shows" where
    "shows_fun_decl fdecl \<equiv> 
      shows dflt_type o shows_space o shows (fun_decl.name fdecl) o 
        shows_paren ( shows_sep shows_arg (shows '', '') (fun_decl.params fdecl)) o
          shows '' {'' o shows_nl o 
            shows_sep shows_local id (fun_decl.locals fdecl) o
            shows_com 1 (fun_decl.body fdecl) o
          shows ''}'' o shows_nl"

subsection \<open>Pretty printing of stack\<close>

text \<open>A single stack frame is pretty printed by printing the command, the local variables and the
  return location expected when a function is called. It must be given a variable name list to
  know what local variables to print.\<close>
  fun shows_stack_frame :: "vname list \<Rightarrow> stack_frame \<Rightarrow> shows" where
    "shows_stack_frame vnames (com,val,rloc) = 
      (shows_com 0 com) o shows_valuation vnames val o shows_nl o shows ''rloc = '' o shows rloc"

text \<open>Pretty printing of the whole stack consists of pretty printing of every stack frame
  separated by "---------------"
\<close>
  definition shows_stack :: "vname list \<Rightarrow> stack_frame list \<Rightarrow> shows" where
    "shows_stack vnames s \<equiv> shows_sep (shows_stack_frame vnames) (shows_nl o shows ''---------------'' o shows_nl) s"


subsection \<open>Pretty printing of state\<close>

text \<open>Pretty printing of the state consists of given a list of variable names, pretty print
  the stack, the globals valuation and the memory separated by "================="\<close>
  fun shows_state :: "vname list \<Rightarrow> state \<Rightarrow> shows" where 
    "shows_state vnames (\<sigma>,\<gamma>,\<mu>) = 
      shows_stack vnames \<sigma> o 
      shows_nl o shows ''================='' o shows_nl o
      shows_valuation vnames \<gamma> o
      shows_nl o shows ''================='' o shows_nl o
      showsp_mem 0 \<mu>
    "

  abbreviation "show_state vnames s \<equiv> shows_state vnames s ''''"

subsection \<open>Pretty printing of global declarations\<close>

text \<open>A declaration of a global variable is done with indentation = 0 and is pretty printed
  as follows:

  <type> <argument_name>;
\<close>
  definition shows_global :: "string \<Rightarrow> shows" where
    "shows_global s \<equiv> indent_basic 0 (shows dflt_type o shows_space o shows s)"


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
      shows_sep shows_global id (program.globals p) o
      shows_nl o
      shows_sep shows_fun_decl shows_nl (program.procs p)"

subsection \<open>Exporting C code\<close>

definition prepare_export :: "program \<Rightarrow> string option" where
  "prepare_export prog \<equiv> do {
    assert (valid_program prog);
    Some (shows_prog prog '''')
  }"

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
