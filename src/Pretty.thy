theory Pretty
imports Eval "Show/Show_Instances"
begin

  definition "dflt_type \<equiv> ''intptr_t''" -- \<open>Important: Must match @{term int_width} !\<close>
  definition "dflt_type_bound_name \<equiv> ''INTPTR''"

  definition "dflt_type_min_bound_name \<equiv> dflt_type_bound_name @ ''_MIN''"
  definition "dflt_type_max_bound_name \<equiv> dflt_type_bound_name @ ''_MAX''"

  definition "preproc_assert_defined a \<equiv> ''#ifndef '' @ a @ ''\<newline>  #error (\"Macro ''@a@'' undefined\")\<newline>#endif\<newline>''"

  definition "preproc_assert_eq a b \<equiv> ''#if ( '' @ a @ '' != '' @ b 
    @ '' )\<newline>  #error (\"Assertion '' @ a @ '' == '' @ b @ '' failed\")\<newline>#endif\<newline>''"

  definition integer_bounds_check :: string where
    "integer_bounds_check \<equiv> 
      preproc_assert_defined dflt_type_min_bound_name
    @ preproc_assert_defined dflt_type_max_bound_name
    @ preproc_assert_eq (dflt_type_min_bound_name @ '' + 1'') (show (INT_MIN + 1))
      (* TODO: Ugly workaround against the absolute value of INT_MIN 
        exceeding INT_MAX of the preprocessor, and the preprocessor interprets -number as -(number),
        and gives a warning it cannot represent number *)
    @ preproc_assert_eq dflt_type_max_bound_name (show INT_MAX)"

  instantiation word :: (len)"show" begin
    definition "shows_prec p w \<equiv> shows_prec p (sint w)"

    definition "shows_list (l::'a word list) \<equiv> showsp_list shows_prec 0 l"

    instance
      apply default
      unfolding shows_prec_word_def[abs_def] shows_list_word_def
      apply (simp_all add: show_law_simps)
      done
  end    

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

  fun showsp_val_option :: "val option showsp" where
    "showsp_val_option _ None = shows ''?''"
  | "showsp_val_option _ (Some v) = shows v"

  fun showsp_block :: "val option list option showsp" where
    "showsp_block _ None = shows ''<free>''"
  | "showsp_block _ (Some l) = showsp_list showsp_val_option 0 l"  

  fun showsp_block_at :: "(nat \<times> val option list option) showsp" where
    "showsp_block_at _ (base, block) = shows base o shows '': '' o showsp_block 0 block"

  definition showsp_mem :: "mem showsp" where
    "showsp_mem _ m \<equiv> shows_sep (showsp_block_at 0) shows_nl (enumerate 0 m)"


  definition shows_valuation :: "vname list \<Rightarrow> valuation \<Rightarrow> shows" where 
    "shows_valuation vnames val \<equiv> let
      shows_pair = (\<lambda>(x,v). shows x o shows '' = '' o showsp_val_option 0 v);
      pairs = map (\<lambda>(x,Some v) \<Rightarrow> (x,v)) (filter (\<lambda>(_,v). v\<noteq>None) (map (\<lambda>x. (x, val x)) vnames))
    in
      showsp_list (\<lambda>_. shows_pair) 0 pairs
      "

  abbreviation "shows_binop s1 opr s2 \<equiv> 
    shows_paren s1 o shows_space o shows opr o shows_space o shows_paren s2"

  abbreviation "shows_unop opr s2 \<equiv> 
    shows opr o shows_space o shows_paren s2"

  definition shows_cast_to_pointer :: "shows \<Rightarrow> shows" where
    "shows_cast_to_pointer s \<equiv> shows_paren ( shows dflt_type o shows ''*'') o s "

  definition shows_cast_to_dflt_type :: "shows \<Rightarrow> shows" where
    "shows_cast_to_dflt_type s \<equiv> shows_paren ( shows dflt_type ) o s "

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
  | "shows_exp (New e) = shows_cast_to_dflt_type ( shows ''malloc (sizeof('' o shows dflt_type o shows '') * '' o shows_paren (shows_exp e) o shows '')'')"
  | "shows_exp (Deref e) = shows ''*'' o shows_paren (shows_cast_to_pointer (shows_exp e))"
  | "shows_exp (Ref e) = shows_cast_to_pointer (shows_unop ''&'' (shows_lexp e))"
  | "shows_exp (Index e1 e2) = shows_paren (shows_cast_to_pointer (shows_exp e1)) o shows CHR ''['' o shows_exp e2 o shows CHR '']''"
  | "shows_lexp (Derefl exp) = 
      (*shows ''&'' o*) shows_paren (shows ''*'' o  shows_paren (shows_cast_to_pointer (shows_exp exp)))"
  | "shows_lexp (Indexl e1 e2) = shows_paren (shows_cast_to_pointer (shows_exp e1)) o shows CHR ''['' o shows_exp e2 o shows CHR '']''"
                                                                             
  abbreviation "indent ind s \<equiv> shows (replicate (ind*2) CHR '' '') o s o shows_nl"
  abbreviation "indent_basic ind s \<equiv> shows (replicate (ind*2) CHR '' '') o s o shows '';'' o shows_nl"

  definition "shows_fun_call fname args \<equiv> 
    shows fname o shows_paren (shows_sep shows_exp (shows '', '') args)"

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

  definition shows_arg :: "string \<Rightarrow> shows" where
    "shows_arg s \<equiv> shows dflt_type o shows_space o shows s"

  definition shows_local :: "string \<Rightarrow> shows" where
    "shows_local s \<equiv> indent_basic 1 (shows dflt_type o shows_space o shows s)"

  definition shows_fun_decl :: "fun_decl \<Rightarrow> shows" where
    "shows_fun_decl fdecl \<equiv> 
      shows dflt_type o shows_space o shows (fun_decl.name fdecl) o 
        shows_paren ( shows_sep shows_arg (shows '', '') (fun_decl.params fdecl)) o
          shows '' {'' o shows_nl o 
            shows_sep shows_local id (fun_decl.locals fdecl) o
            shows_com 1 (fun_decl.body fdecl) o
          shows ''}'' o shows_nl"
          
  fun shows_stack_frame :: "vname list \<Rightarrow> stack_frame \<Rightarrow> shows" where
    "shows_stack_frame vnames (com,val,rloc) = 
      (shows_com 0 com) o shows_valuation vnames val o shows_nl o shows ''rloc = '' o shows rloc"

  definition shows_stack :: "vname list \<Rightarrow> stack_frame list \<Rightarrow> shows" where
    "shows_stack vnames s \<equiv> shows_sep (shows_stack_frame vnames) (shows_nl o shows ''---------------'' o shows_nl) s"

  fun shows_state :: "vname list \<Rightarrow> state \<Rightarrow> shows" where 
    "shows_state vnames (\<sigma>,\<gamma>,\<mu>) = 
      shows_stack vnames \<sigma> o 
      shows_nl o shows ''================='' o shows_nl o
      shows_valuation vnames \<gamma> o
      shows_nl o shows ''================='' o shows_nl o
      showsp_mem 0 \<mu>
    "

  abbreviation "show_state vnames s \<equiv> shows_state vnames s ''''"

  definition shows_global :: "string \<Rightarrow> shows" where
    "shows_global s \<equiv> indent_basic 0 (shows dflt_type o shows_space o shows s)"

  fun filter_procs :: "(fun_decl \<Rightarrow> bool) \<Rightarrow> fun_decl list \<Rightarrow> fun_decl list" where
    "filter_procs f l = undefined"

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
      shows integer_bounds_check o
      shows_nl o shows_nl o
      shows_sep shows_global id (program.globals p) o
      shows_nl o
      shows_sep shows_fun_decl shows_nl (program.procs p)"



ML \<open>
  fun export_c_code code rel_path name thy =
    let 
      val str = code |> String.implode
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
\<close>





end
