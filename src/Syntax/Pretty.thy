theory Pretty
imports 
  Pretty_Program 
  "../Semantics/SmallStep"
  "../Lib/Show/Show_Instances"
begin

section \<open>Pretty Printer\<close>

subsection \<open>Pretty printing of words\<close>

definition shows_int_val :: "int_val \<Rightarrow> shows" where
  "shows_int_val i \<equiv> shows_int_const (sint i)"

subsection \<open>Pretty printing of values\<close>

fun shows_subpath :: "subpath \<Rightarrow> shows" where
  "shows_subpath [] = id"
| "shows_subpath (subscript.Idx n#p) = shows ''['' o shows n o shows '']'' o shows_subpath p"  
| "shows_subpath (subscript.Memb n#p) = shows ''.'' o shows n o shows_subpath p"  

lemma [show_law_simps]: "shows_subpath p (r@s) = shows_subpath p r @ s"
  apply (induction p rule: shows_subpath.induct)
  by (simp_all add: show_law_simps)

definition shows_addr :: "addr \<Rightarrow> shows" where
  "shows_addr \<equiv> \<lambda>(bi,p). shows ''*'' o shows bi o shows_subpath p "

fun shows_val :: "val \<Rightarrow> shows" where
  "shows_val (val.Null) = shows ''null''"
| "shows_val (val.I w) = shows_int_val w"  
| "shows_val (val.Addr addr) = shows_addr addr"
| "shows_val (val.Array vs) = shows ''['' o shows_sep shows_val (shows '', '') vs o shows '']''"
| "shows_val (val.Struct vs) = do {
    let m = map (\<lambda>(n,v). shows n o shows '' = '' o shows_val v) vs;
    shows ''{'' o shows_sep id (shows ''; '') m o shows ''}''
  }"
| "shows_val (val.Uninit) = shows ''<uninit>''"

subsection \<open>Pretty printing of return locations\<close>

primrec shows_return_loc :: "addr option \<Rightarrow> shows" where
  "shows_return_loc None = shows ''<invalid>''"
| "shows_return_loc (Some v) = shows_addr v"

subsection \<open>Pretty printing of @{term "val option"}\<close>

text \<open>A @{term "val option"} means uninitialized if it is @{term None}, and initialized with
  value v it is @{term "Some v"}. If it's @{term None} we pretty print a @{term "''?''"} meaning
  uninitialized.
\<close>
  fun showsp_val_option :: "val option showsp" where
    "showsp_val_option _ None = shows ''?''"
  | "showsp_val_option _ (Some v) = shows_val v"

subsection \<open>Pretty printing of valuations\<close>

definition shows_addr_content :: "memory \<Rightarrow> addr \<Rightarrow> shows" where
  "shows_addr_content \<mu> addr \<equiv> case eget (l_addr addr) \<mu> of
    return v \<Rightarrow> shows_val v | _ \<Rightarrow> shows ''<invalid>''"

text \<open>Given a list of variable names the valuation will be printed with the following format:
  [<vname_0> = <value_0>, <vname_1> = <value_1>, ... , <vname_n> = <value_n>]
\<close>
  definition shows_valuation :: "vname list \<Rightarrow> memory \<Rightarrow> valuation \<Rightarrow> shows" where 
    "shows_valuation vnames \<mu> vs \<equiv> let
      shows_pair = (\<lambda>(x,addr). shows x o shows '' = '' o shows_addr addr o shows_space o shows_paren (shows_addr_content \<mu> addr));
      pairs = map (\<lambda>x. case vs x of None \<Rightarrow> None | Some a \<Rightarrow> Some (x,a)) vnames;
      pairs = filter (Not o op = None) pairs;
      pairs = map the pairs
    in
      showsp_list (\<lambda>_. shows_pair) 0 pairs
      "

  definition shows_res :: "memory \<Rightarrow> res \<Rightarrow> shows" where 
    "shows_res \<mu> r \<equiv> case r of
      res.L addr \<Rightarrow> shows_addr_content \<mu> addr o shows '' [@'' o shows_addr addr o shows '']''
    | res.R v \<Rightarrow> shows_val v"

  definition shows_res' :: "state \<Rightarrow> res \<Rightarrow> shows" where 
    "shows_res' \<equiv> \<lambda>(_,_,\<mu>). shows_res \<mu>"


subsection \<open>Pretty printing of memory\<close>

  fun shows_block :: "mem_block \<Rightarrow> shows" where
    "shows_block (Block ty static v) = (if static then shows ''[static] '' else id) o shows_val v o shows '' :: '' o shows_ty ty"
  | "shows_block (Freed ty) = shows ''<Free>'' o shows '' :: '' o shows_ty ty"  

text \<open>The memory is indexed by an @{term "A (base, ofs)"} in order to print a block we will
  use the following format:

  <block_number> : <block_content>
\<close>
  fun shows_block_at :: "(nat \<times> mem_block) \<Rightarrow> shows" where
    "shows_block_at (base, block) = shows base o shows '': '' o shows_block block"

text \<open>Finally we show every block of the memory following the previous format defined by
  @{term showsp_block_at} separated by new line characters.
\<close>
  definition shows_mem :: "memory \<Rightarrow> shows" where
    "shows_mem m \<equiv> shows_sep (shows_block_at) shows_nl (List.enumerate 0 m)"

subsection \<open>Pretty printing of stack\<close>

text \<open>A single stack frame is pretty printed by printing the command, the local variables and the
  return location expected when a function is called. It must be given a variable name list to
  know what local variables to print.\<close>
  fun shows_stack_frame :: "vname list option \<Rightarrow> memory \<Rightarrow> stack_frame \<Rightarrow> shows" where
    "shows_stack_frame vnames \<mu> (fd,com,val,rloc) = (let
      vnames = case vnames of Some vn \<Rightarrow> vn | None \<Rightarrow> map fst (fun_decl.locals fd)
    in
      shows (fun_decl.name fd) o shows '':'' o shows_nl 
        o (shows_com 1 com) 
        o indent 1 (shows ''locals: '' o shows_valuation vnames \<mu> val o shows_nl) 
        o indent 1 (shows ''rloc: '' o shows_return_loc rloc)
    )"

text \<open>Pretty printing of the whole stack consists of pretty printing of every stack frame
  separated by "---------------"
\<close>
  definition shows_stack :: "vname list option \<Rightarrow> memory \<Rightarrow> stack_frame list \<Rightarrow> shows" where
    "shows_stack vnames \<mu> s \<equiv> shows_sep (shows_stack_frame vnames \<mu>) (shows_nl o shows ''---------------'' o shows_nl) s"


subsection \<open>Pretty printing of state\<close>

text \<open>Pretty printing of the state consists of given a list of variable names, pretty print
  the stack, the globals valuation and the memory separated by "================="\<close>
  fun shows_state :: "program \<Rightarrow> vname list option \<Rightarrow> state \<Rightarrow> shows" where 
    "shows_state p vnames (\<sigma>,\<gamma>,\<mu>) = 
      shows_stack vnames \<mu> \<sigma> o 
      shows_nl o shows ''================='' o shows_nl o
      ( let 
          vnames = case vnames of Some vn \<Rightarrow> vn | None \<Rightarrow> map fst (program.globals p)
        in
          shows_valuation vnames \<mu> \<gamma>
      ) o
      shows_nl o shows ''================='' o shows_nl o
      shows_mem \<mu>
    "

  abbreviation "show_state p vnames s \<equiv> shows_state p vnames s ''''"

subsection \<open>Pretty Printing of Error\<close>
fun shows_error :: "chloe_error \<Rightarrow> shows" where
  "shows_error type_error = shows ''dynamic type error''"
| "shows_error overflow_error = shows ''overflow''"
| "shows_error div_zero_error = shows ''division by zero''"
| "shows_error pointer_error = shows ''pointer error''"
| "shows_error uninitalized_error = shows ''uninitialized value access''"
| "shows_error structural_error = shows ''dynamic structural error''"
                                                                
definition shows_rtype where "shows_rtype \<equiv> \<lambda>
  (False,ty) \<Rightarrow> shows ''r'' o shows_paren (shows_ty ty)
| (True,ty) \<Rightarrow> shows ''l'' o shows_paren (shows_ty ty)"

definition shows_rettype where "shows_rettype \<equiv> \<lambda>
  Some ty \<Rightarrow> shows_ty ty
| None \<Rightarrow> shows ''void''"


term shows_nl

primrec shows_err_msg :: "err_msg \<Rightarrow> shows" where
    "shows_err_msg (ENoStruct sname) = shows ''No such structure '' o shows sname"
  | "shows_err_msg (ENoFun fname) = shows ''No such function '' o shows fname"
  | "shows_err_msg (ENoVar vname) = shows ''No such variable '' o shows vname"
  | "shows_err_msg (ENoMember sname mname) = shows ''Structure '' o shows sname o shows '' has no member '' o shows mname"
  | "shows_err_msg (EConstTooLarge i) = shows ''Integer constant too large/small '' o shows i"
  | "shows_err_msg (EInvalidOp1Type op1 rty) = shows ''Invalid type for operand '' o shows_op1 op1 (shows_rtype rty)"
  | "shows_err_msg (EInvalidOp2Type op2 rty1 rty2) = shows ''Invalid type for operand '' o shows_op2 op2 (shows_rtype rty1) (shows_rtype rty2)"
  | "shows_err_msg (ERefRvalue) = shows ''Rvalue cannot be referenced''"
  | "shows_err_msg (EAssignRval ) = shows ''LHS of assignment must be lvalue''"
  | "shows_err_msg (EAssignTyMismatch ty1 ty2) = shows ''Type mismatch on assignment '' o shows_binop (shows_ty ty1) ''='' (shows_ty ty2)"
  | "shows_err_msg (EArgsMismatch fd tyl1 tyl2) = 
      shows ''Argument mismatch when calling '' 
      o shows (fun_decl.name fd) o shows_paren (shows_sep shows_ty (shows '','') tyl1) 
      o shows '' vs. ''
      o shows_paren (shows_sep shows_ty (shows '','') tyl2)"
  | "shows_err_msg (EAssignFromVoid fd) = shows ''Void function does not return value '' o shows (fun_decl.name fd)"
  | "shows_err_msg (EExpectedInt ty) = shows ''Expected integer operand, but got '' o shows_ty ty "
  | "shows_err_msg (EExpectedIntPtr ty) = shows ''Expected integer or pointer operand, but got '' o shows_ty ty "
  | "shows_err_msg (EFreeExpectsPtr ty) = shows ''Free expects pointer operand, but got '' o shows_ty ty"
  | "shows_err_msg (EReturnTypeMismatch rty1 rty2) = shows ''Return type mismatch: Function declares '' o shows_rettype rty1 o shows '', but got '' o shows_rettype rty2"
  | "shows_err_msg (EExecReachesEndOfNonvoidFun) = shows ''Execution reaches end of non-void function''"
  | "shows_err_msg (EInvalidReturnType ty) = shows ''Invalid return type '' o shows_ty ty"
  | "shows_err_msg (EInvalidParamType ty) = shows ''Invalid parameter type '' o shows_ty ty"
  | "shows_err_msg (EOther string) = shows ''Uncategorized error: '' o shows string"


  fun shows_position :: "position \<Rightarrow> shows" where
    "shows_position (f,e) = 
      (case f of None \<Rightarrow> shows ''-'' | Some fd \<Rightarrow> shows (fun_decl.name fd)) 
    o shows ''@''  
    o (case e of None \<Rightarrow> shows ''-'' | Some e \<Rightarrow> shows_exp e)"


fun shows_ckerror :: "ck_error \<Rightarrow> shows" where
  "shows_ckerror (CKErr p m) = shows ''['' o shows_position p o shows '']: '' o shows_err_msg m"

fun shows_combined_err :: "ck_error + chloe_error \<Rightarrow> shows" where
  "shows_combined_err (Inl e) = shows_ckerror e"
| "shows_combined_err (Inr e) = shows_error e"
  
end
