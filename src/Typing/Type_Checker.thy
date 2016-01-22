theory Type_Checker
imports "../Syntax/Wf_Checker" "../Lib/Option_Monad_Add"
  "../Semantics/Int_Value" (** This dependency is only for representable_int! *)
begin

  subsection \<open>Monad setup for type checker\<close>

  type_synonym position = "fun_decl option \<times> exp option"

  datatype err_msg = 
    ENoStruct sname
  | ENoFun fname
  | ENoVar vname
  | ENoMember sname mname
  | EConstTooLarge int
  | EInvalidOp1Type op1 "bool \<times> ty"
  | EInvalidOp2Type op2 "bool \<times> ty" "bool \<times> ty"
  | ERefRvalue
  | EAssignRval 
  | EAssignTyMismatch ty ty
  | EArgsMismatch fun_decl "ty list" "ty list"
  | EAssignFromVoid fun_decl
  | EExpectedInt ty
  | EExpectedIntPtr ty
  | EFreeExpectsPtr ty
  | EReturnTypeMismatch "ty option" "ty option"
  | EExecReachesEndOfNonvoidFun
  | EInvalidReturnType ty
  | EInvalidParamType ty
  | EOther string

  datatype ck_error = CKErr position err_msg

  abbreviation "mk_ckerr msg \<equiv> CKErr (None,None) msg"
  abbreviation "ckassert \<Phi> msg \<equiv> assert \<Phi> (mk_ckerr msg)"
  
  type_synonym ('a) ck = "('a,ck_error) error"
  type_synonym ('a,'b) ckfun = "'a \<Rightarrow> 'b ck"
  
  locale checker_syntax begin
    no_type_notation cefun (infixr "\<hookrightarrow>" 0)
    type_notation ckfun (infixr "\<hookrightarrow>" 0)
  end

  abbreviation "cklookup E \<equiv> elookup (mk_ckerr o E)"

  type_synonym typing = "vname \<rightharpoonup> ty"

  abbreviation typing_of :: "vdecl list \<Rightarrow> typing" where "typing_of \<equiv> map_of"

  type_synonym res_ty = "bool \<times> ty" -- \<open>Result of expressions: lvalue-flag and type\<close>


  context program_defs_loc begin
    abbreviation "GT \<equiv> typing_of (program.globals \<pi>)"
  end

  context
    fixes p :: program
  begin  

    interpretation checker_syntax .
    interpretation program_defs_loc p .

    abbreviation resolve_sname :: "sname \<hookrightarrow> mdecl list" where
      "resolve_sname \<equiv> cklookup ENoStruct SM"

    definition resolve_fname :: "sname \<hookrightarrow> fun_decl" where
      "resolve_fname \<equiv> cklookup ENoFun FM"

    definition resolve_mname :: "sname \<Rightarrow> mdecl list \<Rightarrow> mname \<hookrightarrow> ty" where
      "resolve_mname sn mts \<equiv> cklookup (ENoMember sn) (map_of mts)"

    context 
      fixes fdecl :: fun_decl
    begin  
      definition "ET \<equiv> 
        GT ++
        typing_of (fun_decl.params fdecl @ fun_decl.locals fdecl)"
      definition "RT \<equiv> fun_decl.rtype fdecl"  

      (*lemma "ET x =
        typing_of (fun_decl.params fdecl @ fun_decl.locals fdecl) x
        orelse GT x"
        unfolding ET_def
        by (auto simp: map_add_apply)*)

      definition varty :: "vname \<hookrightarrow> ty" where
        "varty \<equiv> cklookup ENoVar ET"

      text \<open>Types of expressions are normalized to replace struct-pointers by pointers  
          at the topmost level. This is necessary due to our implementation choice of
          having types as finite data types, and thus modeling cyclic structure pointers
          by explicit indirection through naming. \<close>  
      fun norm_struct_ptr :: "res_ty \<hookrightarrow> res_ty" where
        "norm_struct_ptr (lv,ty.StructPtr sname) = do {
          mts \<leftarrow> resolve_sname sname; 
          return (lv,ty.Ptr (ty.Struct sname mts))}"
      | "norm_struct_ptr rty = return rty"    

      lemma norm_struct_ptr_pres_lv[simp]: 
        "norm_struct_ptr (lv,T) = return (lv',T') \<Longrightarrow> lv'=lv"  
        apply (cases "(lv,T)" rule: norm_struct_ptr.cases)
        apply (auto split: Error_Monad.bind_splits)
        done


      text \<open>Convert array to pointer type, if it occurs as operand of an operator other than 
        @{text "&"}. 
          (C99, 6.3.2.3)\<close>
      fun norm_array_ty :: "ty \<Rightarrow> ty" where
        "norm_array_ty (ty.Array _ ty) = (ty.Ptr ty)"
      | "norm_array_ty ty = ty"  



      fun ty_op0 :: "op0 \<hookrightarrow> res_ty" where
        "ty_op0 (op0.Const i) = do {
          ckassert (representable_int i) (EConstTooLarge i);
            return (False,ty.I) 
        }"
      | "ty_op0 op0.Null = return (False,ty.Null)"  
      | "ty_op0 (op0.Var x) = do {ty \<leftarrow> varty x; return (True,ty)}"


      fun ty_op1 :: "op1 \<Rightarrow> res_ty \<hookrightarrow> res_ty" where
        "ty_op1 op1.UMinus (_,ty.I) = return (False,ty.I)"
      | "ty_op1 op1.Not (_,ty.I) = return (False,ty.I)"  
      | "ty_op1 op1.BNot (_,ty.I) = return (False,ty.I)"
      | "ty_op1 op1.Deref (_,ty.Ptr ty) = return (True,ty)" 
      (*| "ty_op1 op1.Deref (True,ty.Array _ ty) = return (True,ty)" *)
      | "ty_op1 op1.Ref (lv,T) = do {
            ckassert lv (ERefRvalue);
            ckassert (\<not>ty.is_Array T) (EOther ''Referencing of array''); (* Although conforming to C99, we explicitly 
              exclude pointers to arrays here. *)
            return (False,ty.Ptr T)
         }"
      | "ty_op1 (op1.Memb name) (True,ty.Struct sname mts) = do {
          ty \<leftarrow> resolve_mname sname mts name; 
          return (True,ty)}"
      | "ty_op1 (op1.Membp name) (_,ty.Ptr (ty.Struct sname mts)) = do {
          ty \<leftarrow> resolve_mname sname mts name; 
          return (True,ty)}"
      | "ty_op1 op1 ty = EAssert (mk_ckerr (EInvalidOp1Type op1 ty))"

      fun ty_arith_binop :: "ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_arith_binop (ty.I) (ty.I) = Some (False,ty.I)"
      | "ty_arith_binop _ _ = None"  

      fun ty_arith_comp :: "ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_arith_comp (ty.I) (ty.I) = Some (False,ty.I)"
      | "ty_arith_comp _ _ = None"  
      
      fun ty_ptr_add :: "ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_ptr_add (ty.Ptr T) (ty.I) = Some (False,ty.Ptr T)"
      (*| "ty_ptr_add (ty.Array _ T) (ty.I) = Some (False,ty.Ptr T)"*) 
      | "ty_ptr_add _ _ = None"
      
      fun ty_ptr_diff :: "ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_ptr_diff (ty.Ptr T) (ty.Ptr T') = do { oassert (T=T'); Some (False,ty.I) }"
      | "ty_ptr_diff _ _ = None"

      fun ty_ptr_comp :: "ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_ptr_comp (ty.Ptr T) (ty.Ptr T') = do { oassert (T=T'); Some (False,ty.I) }"
      | "ty_ptr_comp _ _ = None"

      fun ty_ptr_eq :: "ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_ptr_eq (ty.Ptr T) (ty.Ptr T') = do { oassert (T=T'); Some (False,ty.I) }"
      | "ty_ptr_eq (ty.Ptr T) (ty.Null) = (Some (False,ty.I))"
      | "ty_ptr_eq (ty.Null) (ty.Ptr T') = (Some (False,ty.I))"
      | "ty_ptr_eq (ty.Null) (ty.Null) = (Some (False,ty.I))"
      | "ty_ptr_eq _ _ = None"

      fun ty_index :: "ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_index (ty.Ptr T) (ty.I) = Some (True,T)"
      | "ty_index _ _ = None"

      private abbreviation try_op2 
        :: "(ty \<Rightarrow> ty \<rightharpoonup> res_ty) list \<Rightarrow> ty \<Rightarrow> ty \<rightharpoonup> res_ty"
      where "try_op2 l e1 e2 \<equiv> FIRST (map (\<lambda>f. f (norm_array_ty e1) (norm_array_ty e2)) l)"  

      primrec ty_op2_aux :: "op2 \<Rightarrow> ty \<Rightarrow> ty \<rightharpoonup> res_ty" where
        "ty_op2_aux op2.Plus = try_op2 [ty_arith_binop, ty_ptr_add]"
      | "ty_op2_aux op2.Minus = try_op2 [ty_arith_binop, ty_ptr_diff]"
      | "ty_op2_aux op2.Mult = ty_arith_binop"
      | "ty_op2_aux op2.Div = ty_arith_binop"
      | "ty_op2_aux op2.Mod = ty_arith_binop"
      | "ty_op2_aux op2.Less = try_op2 [ty_arith_comp, ty_ptr_comp]"
      | "ty_op2_aux op2.Leq = try_op2 [ty_arith_comp, ty_ptr_comp]"
      | "ty_op2_aux op2.Eq = try_op2 [ty_arith_comp, ty_ptr_eq]"
      | "ty_op2_aux op2.And = ty_arith_binop"
      | "ty_op2_aux op2.Or = ty_arith_binop"
      | "ty_op2_aux op2.BAnd = ty_arith_binop"
      | "ty_op2_aux op2.BOr = ty_arith_binop"
      | "ty_op2_aux op2.BXor = ty_arith_binop"
      | "ty_op2_aux op2.Index = ty_index"

      definition ty_op2 :: "op2 \<Rightarrow> res_ty \<Rightarrow> res_ty \<hookrightarrow> res_ty" where
        "ty_op2 op2 \<equiv> \<lambda>(lv1,ty1) (lv2,ty2). case ty_op2_aux op2 ty1 ty2 of 
          Some rty \<Rightarrow> return rty
        | None \<Rightarrow> EAssert (mk_ckerr (EInvalidOp2Type op2 (lv1,ty1) (lv2,ty2)))"
        

      primrec ty_exp_aux :: "exp \<hookrightarrow> res_ty" where
        "ty_exp_aux (exp.E0 f) = ty_op0 f \<bind> norm_struct_ptr"
      | "ty_exp_aux (exp.E1 f e) = do {
          ty \<leftarrow> ty_exp_aux e;
          ty \<leftarrow> ty_op1 f ty;
          norm_struct_ptr ty
        }"  
      | "ty_exp_aux (exp.E2 f e1 e2) = do {
          ty1 \<leftarrow> ty_exp_aux e1;
          ty2 \<leftarrow> ty_exp_aux e2;
          ty \<leftarrow> ty_op2 f ty1 ty2;
          norm_struct_ptr ty
        }"  

      definition ty_exp :: "exp \<hookrightarrow> res_ty" where
        "ty_exp e \<equiv> case ty_exp_aux e of
          return x \<Rightarrow> return x
        | EAssert (CKErr (f,None) m) \<Rightarrow> EAssert (CKErr (f,Some e) m)
        | r \<Rightarrow> r"


      definition ty_assign' :: "ty \<Rightarrow> ty \<hookrightarrow> unit" where
        "ty_assign' ty1 ty2 \<equiv> do {
          let ty2 = norm_array_ty ty2;
          ckassert (ty1 = ty2 \<or> is_Ptr ty1 \<and> ty2=ty.Null) (EAssignTyMismatch ty1 ty2)
        }"

      definition ty_assign :: "res_ty \<Rightarrow> res_ty \<hookrightarrow> unit" where
        "ty_assign rty1 rty2 \<equiv> do {
          let (lv1,ty1) = rty1;
          let (_,ty2) = rty2;
          ckassert lv1 EAssignRval;
          ty_assign' ty1 ty2
        }"
        
      definition assert_int_exp :: "exp \<hookrightarrow> unit" where "
        assert_int_exp e \<equiv> do {
          (_,ty) \<leftarrow> ty_exp e;
          assert (ty=ty.I) (CKErr (None,Some e) (EExpectedInt ty))
        }"

      definition assert_int_ptr_exp :: "exp \<hookrightarrow> unit" where "
        assert_int_ptr_exp e \<equiv> do {
          (_,ty) \<leftarrow> ty_exp e;
          assert (ty=ty.I \<or> ty=ty.Null \<or> is_Ptr ty) (CKErr (None,Some e) (EExpectedIntPtr ty))
        }"
  
      definition "args_compat fd args \<equiv> do {
        argst \<leftarrow> emap ty_exp args;
        let argst = map snd argst;
        let paramt = map snd (fun_decl.params fd);
        ckassert (paramt = argst) (EArgsMismatch fd paramt argst)
        }"
        
      definition "fun_compatv f args \<equiv> do {
        fdecl \<leftarrow> resolve_fname f;
        args_compat fdecl args
      }"  
    
      definition "fun_compat le f args \<equiv> do {
        rty1 \<leftarrow> ty_exp le;
        fdecl \<leftarrow> resolve_fname f;
        args_compat fdecl args;
        ty2 \<leftarrow> o2e (mk_ckerr (EAssignFromVoid fdecl)) (fun_decl.rtype fdecl);
        ty_assign rty1 (False,ty2)
      }"  

      (*text \<open>
        We restrict the types that can be passed to malloc to non-array types.
        We also disallow direct or indirect pointers to arrays
        \<close>
      fun valid_malloc_type :: "ty \<Rightarrow> bool" where
        "valid_malloc_type (ty.I) \<longleftrightarrow> True"
      | "valid_malloc_type ((ty.Ptr ty)) \<longleftrightarrow> valid_malloc_type ty"  
      | "valid_malloc_type ((ty.StructPtr _)) \<longleftrightarrow> True"
      | "valid_malloc_type ((ty.Struct _ _)) \<longleftrightarrow> True"
      | "valid_malloc_type ((ty.Null)) \<longleftrightarrow> False"
      | "valid_malloc_type ((ty.Array _ _)) \<longleftrightarrow> False"
      *)


      fun ty_com1 :: "com \<hookrightarrow> unit" where
        "ty_com1 com.Skip = return ()"
      | "ty_com1 (com_Assign le re) = do {
          rty1 \<leftarrow> ty_exp le;
          rty2 \<leftarrow> ty_exp re;
          ty_assign rty1 rty2
        }"  
      | "ty_com1 (com.Seq c1 c2) = do {ty_com1 c1; ty_com1 c2}"  
      | "ty_com1 (com.If b c1 c2) = do {
          assert_int_ptr_exp b;
          ty_com1 c1;
          ty_com1 c2
        }"
      | "ty_com1 (com.While b c) = do {
          assert_int_ptr_exp b;
          ty_com1 c
        }"
      | "ty_com1 (com_Malloc e1 ty e2) = do {
          rty1 \<leftarrow> ty_exp e1;
          assert_int_exp e2;
          ty_assign rty1 (False,ty.Ptr ty)
        }"  
      | "ty_com1 (com_Free e) = do {
          (_,ty) \<leftarrow> ty_exp e;
          let ty = norm_array_ty ty;
          assert (is_Ptr ty) (CKErr (None,Some e) (EFreeExpectsPtr ty))
        }"  
      | "ty_com1 (com_Return e) = do {
          (_,ty) \<leftarrow> ty_exp e;
          let ty = norm_array_ty ty;
          ckassert (RT = Some ty) (EReturnTypeMismatch RT (Some ty))
        }"  
      | "ty_com1 com_Returnv = ckassert (RT = None) (EReturnTypeMismatch RT None)"  
      | "ty_com1 (com_Callfun e f args) = fun_compat e f args"
      | "ty_com1 (com_Callfunv f args) = fun_compatv f args"
        
  
      fun ty_com2 :: "com \<Rightarrow> bool" where
        "ty_com2 com.Skip \<longleftrightarrow> RT=None"
      | "ty_com2 (com_Assign _ _) \<longleftrightarrow> RT=None"
      | "ty_com2 (com.Seq _ c2) \<longleftrightarrow> ty_com2 c2"
      | "ty_com2 (com.If _ c1 c2) \<longleftrightarrow> ty_com2 c1 \<and> ty_com2 c2"
      | "ty_com2 (com.While _ _) \<longleftrightarrow> RT=None"
      | "ty_com2 (com_Malloc _ _ _) \<longleftrightarrow> RT=None"
      | "ty_com2 (com_Free _) \<longleftrightarrow> RT=None"
      | "ty_com2 (com_Return _) \<longleftrightarrow> True"
      | "ty_com2 (com_Returnv) \<longleftrightarrow> True"
      | "ty_com2 (com_Callfun _ _ _) \<longleftrightarrow> RT=None"
      | "ty_com2 (com_Callfunv _ _) \<longleftrightarrow> RT=None"

      definition ty_com :: "com \<hookrightarrow> unit" where
        "ty_com c \<equiv> do {
          ty_com1 c;  
          ckassert (ty_com2 c) EExecReachesEndOfNonvoidFun
        }"


      text \<open>Types that are valid as return or parameter types.
        C99: 6.7.5.3.1: Return type must not be array types.

        Additionally, we do not allow @{text "void*"}, and we do not allow
        these types for parameter types as well. According to 
        C99: 6.7.5.3.1 array parameter types shall be treated as pointer types.
        \<close>  
      fun valid_rp_type :: "ty \<Rightarrow> bool" where
        "valid_rp_type (ty.I) \<longleftrightarrow> True"
      | "valid_rp_type ((ty.Ptr ty)) \<longleftrightarrow> True"  
      | "valid_rp_type ((ty.StructPtr _)) \<longleftrightarrow> True"
      | "valid_rp_type ((ty.Struct _ _)) \<longleftrightarrow> True"
      | "valid_rp_type ((ty.Null)) \<longleftrightarrow> False"
      | "valid_rp_type ((ty.Array _ _)) \<longleftrightarrow> False"


      definition ty_fdecl :: "unit ck" where
        "ty_fdecl \<equiv> do {
          ty_com (fun_decl.body fdecl);
          (case RT of 
            None \<Rightarrow> return () 
          | Some ty \<Rightarrow> ckassert (valid_rp_type ty) (EInvalidReturnType ty));
          efold (\<lambda>(_,ty) _. 
            ckassert (valid_rp_type ty) (EInvalidParamType ty)
          ) (fun_decl.params fdecl) ()
        }"

    end  

    definition "ty_program \<equiv> efold (\<lambda>fd _. 
      case ty_fdecl fd of
        EAssert (CKErr (None,e) m) \<Rightarrow> EAssert (CKErr (Some fd,e) m)
      | x \<Rightarrow> x  
    ) (program.functs p) ()"

    definition "wt_program \<equiv> do {
      ckassert (wf_program p) (EOther ''Well-formedness check failed'');
      ty_program
    }"
  end

  export_code wt_program in SML module_name WT_Checker

  locale wt_program_loc = wf_program_loc \<pi> for \<pi> :: program +
    assumes TY[simp]: "ty_program \<pi> = return ()"
  begin
    lemma WT[simp]: "wt_program \<pi> = return ()"
      unfolding wt_program_def
      by simp

    lemma ty_fdeclI:
      assumes "mk_fun_map \<pi> name = Some fd"
      shows "ty_fdecl \<pi> fd = return ()"
      using assms WT 
      unfolding wt_program_def ty_program_def
      apply (auto 
        simp: wt_program_def mk_fun_map_def
        dest!: map_of_SomeD)
      apply (drule (1) bspec)
      apply (auto split: error.splits pre_error.splits ck_error.splits option.splits)
      done

  end


end
