section \<open>Evaluation of Expressions\<close>
theory Eval
imports 
  "../Syntax/Program" Arith Memory
begin


  text \<open>We start with defining a local configuration, that is the 
    configuration as seen within a function context.

    It consists of valuations for the global variables, and for the local 
    variables and parameters. 

    A valuation maps variables to their addresses in memory
  \<close>

  type_synonym valuation = "vname \<rightharpoonup> addr"

  (* TODO: Move this to program evaluator *)
  text \<open>A valuation can be initialized from a variable declaration list,
    by allocating a new block of memory for each variable.\<close>
  definition alloc_vdecls :: "vdecl list \<Rightarrow> memory \<hookrightarrow> (valuation\<times>memory)" where
    "alloc_vdecls l \<mu> \<equiv> efold (\<lambda>(vname,ty) (vals,\<mu>). do {
      (addr,\<mu>) \<leftarrow> alloc ty \<mu>;
      let vals = vals(vname \<mapsto> addr);
      return (vals,\<mu>)
      }) l (Map.empty,\<mu>)"
  
  text \<open>A valuation can also be initialized from a parameter declaration list and a value list\<close>      
  definition alloc_params :: "vdecl list \<Rightarrow> val list \<Rightarrow> memory \<hookrightarrow> (valuation\<times>memory)" where
    "alloc_params vdecls vs \<mu> \<equiv> do {
      assert (length vdecls = length vs) structural_error;
      efold (\<lambda>((name,ty),v) (vals,\<mu>). do {
        (addr,\<mu>) \<leftarrow> cp_alloc ty v \<mu>;
        let vals = vals(name \<mapsto> addr);
        return (vals,\<mu>)
      }) (zip vdecls vs) (Map.empty,\<mu>)
    }"


  text \<open>The result of an evaluation can either be an 
    lvalue, represented by an address, or a plain value (right value)
  \<close>  

  datatype res = L addr | R val
  hide_const (open) L R

  (* TODO: Move *)
  abbreviation (input) e_then (infixr "#>" 54) where "e_then f g \<equiv> \<lambda>x. Error_Monad.bind (f x) g"

  context 
    fixes EV :: valuation -- \<open>Effective valuation, combined globals,locals,params\<close>
    fixes \<mu> :: memory -- \<open>Memory content. Note that expressions do not modify memory 
      in our simple fragment. This saves us from reasoning about sequence points and the order
      in which effects become visible.\<close>
  begin

    primrec to_rval :: "res \<hookrightarrow> val"
      -- \<open>Convert operand to plain value, and array to pointer\<close>
    where
      "to_rval (res.L addr) = do { 
        r \<leftarrow> eget (l_addr addr) \<mu>; 
        assert (r\<noteq>val.Uninit) uninitalized_error; 

        if (val.is_Array r) then do {
          addr \<leftarrow> cnv_array_to_eptr \<mu> addr;
          return (val.Addr addr)
        } else
          return r 
        }"
    | "to_rval (res.R v) = do {
        assert (v\<noteq>val.Uninit) uninitalized_error; 
        return v
      }"

    primrec to_lval :: "res \<hookrightarrow> addr"
      -- \<open>Convert operand to plain value\<close>
    where
      "to_lval (res.L addr) = return addr"
    | "to_lval (res.R v) = EAssert type_error"
  
    fun to_int_aux :: "val \<hookrightarrow> int_val" where
      "to_int_aux (val.I i) = return i"
    | "to_int_aux _ = EAssert type_error"  

    fun to_bool_aux :: "val \<hookrightarrow> bool" where
      "to_bool_aux (val.I i) = return (i2b i)"
    | "to_bool_aux (val.Addr addr) = do { 
        assert (is_allocated \<mu> addr) pointer_error; 
        return True
      }"
    | "to_bool_aux (val.Null) = return False"
    | "to_bool_aux _ = EAssert type_error"  
 
    definition "to_int \<equiv> to_rval #> to_int_aux"
  
    definition "un_arith_op f r \<equiv> do {
      i \<leftarrow> to_int r;
      i \<leftarrow> f i;
      return (res.R (val.I i))
    }"
  
    definition to_ptr :: "res \<hookrightarrow> addr" where
      "to_ptr x \<equiv> do {
        x \<leftarrow> to_rval x;
        case x of 
          val.Addr addr \<Rightarrow> return (addr)
        | val.Null \<Rightarrow> EAssert pointer_error
        | _ \<Rightarrow> EAssert type_error
      }"


    primrec eval0 :: "op0 \<hookrightarrow> res" where
      "eval0 (op0.Const i) = do {v \<leftarrow> mk_repr i; return (res.R (val.I v))}"
    | "eval0 (op0.Null) = return (res.R val.Null)"  
    | "eval0 (op0.Var x) = (case EV x of
        None \<Rightarrow> EAssert type_error
      | Some addr \<Rightarrow> return (res.L addr)
      )"

    definition deref_op :: "res \<hookrightarrow> res" where 
      "deref_op x \<equiv> do {
        addr \<leftarrow> to_ptr x;
        return (res.L addr)
      }"

    primrec ref_op :: "res \<hookrightarrow> res" where 
      "ref_op (res.L addr) = return (res.R (val.Addr addr))"
    | "ref_op (res.R _) = EAssert type_error"

    fun memb_op :: "mname \<Rightarrow> res \<hookrightarrow> res" where 
      "memb_op name (res.L addr) = do {
        addr \<leftarrow> memb_addr \<mu> name addr;
        return (res.L addr)
      }"
    (*| "memb_op name (res.R (val.Struct ms)) = do {
        v \<leftarrow> elookup (\<lambda>_. type_error) (map_of ms) name;
        return (res.R v)
      }"*)  
    | "memb_op _ (res.R _) = EAssert type_error"

    definition membp_op :: "mname \<Rightarrow> res \<hookrightarrow> res" where 
      "membp_op name r = do {
        r \<leftarrow> deref_op r;
        memb_op name r
      }"

    primrec eval1 :: "op1 \<Rightarrow> res \<hookrightarrow> res" where
      "eval1 op1.UMinus v = un_arith_op iop_uminus v"
    | "eval1 op1.Not v = un_arith_op iop_Not v"  
    | "eval1 op1.BNot v = un_arith_op iop_BNot v"  
    | "eval1 op1.Deref v = deref_op v"  
    | "eval1 op1.Ref v = ref_op v"  
    | "eval1 (op1.Memb name) v = memb_op name v"
    | "eval1 (op1.Membp name) v = membp_op name v"

    definition "rvop2 f v1 v2 \<equiv> do { v1 \<leftarrow> to_rval v1; v2 \<leftarrow> to_rval v2; f v1 v2 }"

    fun plus_op :: "val \<Rightarrow> val \<hookrightarrow> res" where
      "plus_op (val.Addr addr) (val.I i) = do {
        let i = sint i;
        addr \<leftarrow> index_addr \<mu> i addr;
        return (res.R (val.Addr addr))
      }"
    | "plus_op (val.Null) (val.I _) = EAssert pointer_error"  
    | "plus_op (val.I x1) (val.I x2) = do {
        r \<leftarrow> iop_plus x1 x2;
        return (res.R (val.I r))
      }"  
    | "plus_op _ _ = EAssert type_error"  

    fun minus_op :: "val \<Rightarrow> val \<hookrightarrow> res" where
      "minus_op (val.Addr addr1) (val.Addr addr2) = do {
        i \<leftarrow> diff_addr \<mu> addr1 addr2;
        i \<leftarrow> mk_repr i;
        return (res.R (val.I i))
      }"
    | "minus_op (val.Null) (val.Addr _) = EAssert pointer_error"  
    | "minus_op (val.Addr _) (val.Null) = EAssert pointer_error"  
    | "minus_op (val.Null) (val.Null) = EAssert pointer_error"  
    | "minus_op (val.I x1) (val.I x2) = do {
        r \<leftarrow> iop_minus x1 x2;
        return (res.R (val.I r))
      }"  
    | "minus_op _ _ = EAssert type_error"  


    fun eq_op :: "val \<Rightarrow> val \<hookrightarrow> res" where
      "eq_op (val.Addr addr1) (val.Addr addr2) = do {
        r \<leftarrow> addr_eq \<mu> addr1 addr2;
        return (res.R (val.I (b2i r)))
      }"
    | "eq_op (val.Addr _) (val.Null) = return (res.R (val.I (b2i False)))"  
    | "eq_op (val.Null) (val.Addr _) = return (res.R (val.I (b2i False)))"  
    | "eq_op (val.Null) (val.Null) = return (res.R (val.I (b2i True)))"  
    | "eq_op (val.I x1) (val.I x2) = do {
        r \<leftarrow> iop_eq x1 x2;
        return (res.R (val.I r))
      }"  
    | "eq_op _ _ = EAssert type_error"  


    fun less_op :: "val \<Rightarrow> val \<hookrightarrow> res" where
      "less_op (val.Addr addr1) (val.Addr addr2) = do {
        r \<leftarrow> addr_less \<mu> addr1 addr2;
        return (res.R (val.I (b2i r)))
      }"
    | "less_op (val.Addr _) (val.Null) = EAssert pointer_error"  
    | "less_op (val.Null) (val.Addr _) = EAssert pointer_error"  
    | "less_op (val.Null) (val.Null) = return (res.R (val.I (b2i False)))"  
    | "less_op (val.I x1) (val.I x2) = do {
        r \<leftarrow> iop_less x1 x2;
        return (res.R (val.I r))
      }"  
    | "less_op _ _ = EAssert type_error"  

    fun le_op :: "val \<Rightarrow> val \<hookrightarrow> res" where
      "le_op (val.Addr addr1) (val.Addr addr2) = do {
        r \<leftarrow> addr_leq \<mu> addr1 addr2;
        return (res.R (val.I (b2i r)))
      }"
    | "le_op (val.Addr _) (val.Null) = EAssert pointer_error"  
    | "le_op (val.Null) (val.Addr _) = EAssert pointer_error"  
    | "le_op (val.Null) (val.Null) = return (res.R (val.I (b2i True)))"  
    | "le_op (val.I x1) (val.I x2) = do {
        r \<leftarrow> iop_le x1 x2;
        return (res.R (val.I r))
      }"  
    | "le_op _ _ = EAssert type_error"  


    definition "bin_arith_op f r1 r2 \<equiv> do {
      i1 \<leftarrow> to_int r1;
      i2 \<leftarrow> to_int r2;
      i \<leftarrow> f i1 i2;
      return (res.R (val.I i))
    }"

    definition "index_op v1 v2 \<equiv> do {
      r \<leftarrow> plus_op v1 v2;
      r \<leftarrow> deref_op r;
      return r
    }"


    primrec eval2 :: "op2 \<Rightarrow> res \<Rightarrow> res \<hookrightarrow> res" where
      "eval2 op2.Plus v1 v2 = rvop2 plus_op v1 v2"
    | "eval2 op2.Minus v1 v2 = rvop2 minus_op v1 v2"  

    | "eval2 op2.Mult v1 v2 = bin_arith_op iop_mult v1 v2"  
    | "eval2 op2.Div v1 v2 = bin_arith_op iop_div v1 v2"  
    | "eval2 op2.Mod v1 v2 = bin_arith_op iop_mod v1 v2"  
    
    | "eval2 op2.Less v1 v2 = rvop2 less_op v1 v2"  
    | "eval2 op2.Leq v1 v2 = rvop2 le_op v1 v2"  
    | "eval2 op2.Eq v1 v2 = rvop2 eq_op v1 v2"  

    | "eval2 op2.And v1 v2 = bin_arith_op iop_And v1 v2"  
    | "eval2 op2.Or v1 v2 = bin_arith_op iop_Or v1 v2"  
    | "eval2 op2.BAnd v1 v2 = bin_arith_op iop_BAnd v1 v2"  
    | "eval2 op2.BOr v1 v2 = bin_arith_op iop_BOr v1 v2"  
    | "eval2 op2.BXor v1 v2 = bin_arith_op iop_BXor v1 v2"  

    | "eval2 op2.Index v1 v2 = rvop2 index_op v1 v2"

    primrec eval_exp :: "exp \<hookrightarrow> res" where
      "eval_exp (exp.E0 f) = eval0 f"
    | "eval_exp (exp.E1 f e) = do {
        r \<leftarrow> eval_exp e;
        eval1 f r
      }"
    | "eval_exp (exp.E2 f e1 e2) = do {
        r1 \<leftarrow> eval_exp e1;
        r2 \<leftarrow> eval_exp e2;   (* TODO/FIXME: We loose short-circuit semantics, i.e., 
          the behaviour of both expressions must be defined. As expressions have no 
          side effects, this only limits the defined expressions, but does not introduce
          non-conforming defined behaviour. *)
        eval2 f r1 r2
      }"

    text \<open>C99: 6.5.2.1.2: The definition of the subscript operator $[]$ is that $E1[E2]$ is identical to $(*((E1)+(E2)))$\<close>  
    lemma index_alt_repr: "eval_exp (exp.E2 op2.Index v1 v2) = eval_exp (exp.E1 op1.Deref (exp.E2 op2.Plus v1 v2))"  
      by (simp add: index_op_def[abs_def] rvop2_def)


  end  

  code_thms eval_exp
  export_code eval_exp checking SML

end

