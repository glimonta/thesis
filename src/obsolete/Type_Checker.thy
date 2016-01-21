theory Type_Checker
imports Exp Com
begin

  fun o_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a list \<rightharpoonup> 'b list" where
    "o_map _ [] = Some []"
  | "o_map f (x#xs) = do { y \<leftarrow> f x; ys \<leftarrow> o_map f xs; Some (y#ys) }"  

  fun (in -) o2b :: "unit option \<Rightarrow> bool" where 
    "o2b None = False"
  | "o2b (Some _) = True"  

  lemma (in -) o2b_alt: "o2b m \<longleftrightarrow> m\<noteq>None" by (cases m) auto
   

  type_synonym typing = "vname \<rightharpoonup> type"

  definition typing_of :: "(type \<times> vname) list \<Rightarrow> typing" where
    "typing_of l \<equiv> map_of (map (\<lambda>(t,v). (v,t)) l)"

  definition (in program_loc) "GT \<equiv> typing_of (program.globals p)"

  context program_loc begin

    context 
      fixes fdecl :: fun_decl
    begin  
      definition "LT \<equiv> typing_of (fun_decl.params fdecl @ fun_decl.locals fdecl)"  
      definition "RT \<equiv> fun_decl.rtype fdecl"  
  
      definition read_varty :: "vname \<rightharpoonup> type"
        where "read_varty x = do {
          case LT x of 
            Some t \<Rightarrow> Some t
          | None \<Rightarrow> GT x
        }"
  
      abbreviation "assert_int t \<equiv> assert (t=TInt)"
      abbreviation "assert_ptr t \<equiv> assert (is_TPtr t)"
    
      context begin  
        private abbreviation bin_int_op :: "_ \<Rightarrow> exp \<Rightarrow> exp \<rightharpoonup> type"
        where 
          "bin_int_op tyeval e1 e2 \<equiv> 
            tyeval e1 \<guillemotright>= (\<lambda>t1. 
            tyeval e2 \<guillemotright>= (\<lambda>t2.
            assert_int t1 \<guillemotright>
            assert_int t2 \<guillemotright>
            Some TInt))
          "
      
        fun tyeval :: "exp \<rightharpoonup> type"
          and tyeval_l :: "lexp \<rightharpoonup> type"
        where
          "tyeval (Const c) = Some TInt"
        | "tyeval Null = Some TNull"  
        | "tyeval (V x) = read_varty x"
        | "tyeval (Plus e1 e2) = do {
            t1\<leftarrow>tyeval e1;
            t2\<leftarrow>tyeval e2;
            case (t1,t2) of
              (TInt,TInt) \<Rightarrow> Some TInt
            | (TPtr t, TInt) \<Rightarrow> Some (TPtr t)
            | (TNull, TInt) \<Rightarrow> None  (* Here, type-checker rejects addition to null constant!*)
            | _ \<Rightarrow> None
          }"
        | "tyeval (Subst e1 e2) = do {
            t1\<leftarrow>tyeval e1;
            t2\<leftarrow>tyeval e2;
            case (t1,t2) of
              (TInt,TInt) \<Rightarrow> Some TInt
            | (TPtr T, TInt) \<Rightarrow> Some (TPtr T)
            | (TPtr T1, TPtr T2) \<Rightarrow> do { assert (T1=T2); Some (TInt) }
            | (TNull, _) \<Rightarrow> None  (* Here, type-checker rejects subtraction of null constant!*)
            | (_,TNull) \<Rightarrow> None  (* Here, type-checker rejects subtraction of null constant!*)
            | _ \<Rightarrow> None
          }"
        | "tyeval (Minus e) = do { t \<leftarrow> tyeval e; assert_int t; Some TInt }"  
        | "tyeval (Div e1 e2) = bin_int_op tyeval e1 e2"  
        | "tyeval (Mod e1 e2) = bin_int_op tyeval e1 e2"  
        | "tyeval (Mult e1 e2) = bin_int_op tyeval e1 e2"  
        | "tyeval (Less e1 e2) = bin_int_op tyeval e1 e2"  (* TODO: Ptr comparison!? *)
        | "tyeval (Not e) = do { t \<leftarrow> tyeval e; assert_int t; Some TInt }"  
        | "tyeval (And e1 e2) = bin_int_op tyeval e1 e2"  
        | "tyeval (Or e1 e2) = bin_int_op tyeval e1 e2"  
        | "tyeval (Eq e1 e2) = do {
            t1\<leftarrow>tyeval e1;
            t2\<leftarrow>tyeval e2;
            case (t1,t2) of
              (TInt,TInt) \<Rightarrow> Some TInt
            | (TPtr _, TNull) \<Rightarrow> Some TInt
            | (TNull, TPtr _) \<Rightarrow> Some TInt
            | (TPtr t, TPtr t') \<Rightarrow> if t=t' then Some TInt else None
            | _ \<Rightarrow> None
          }"
        | "tyeval (New t e) = do {
            tyeval e \<guillemotright>= assert_int;
            Some (TPtr t)
          }"  
        | "tyeval (Deref e) = do {
            t \<leftarrow> tyeval e;
            case t of TPtr t' \<Rightarrow> Some t' | _ \<Rightarrow> None
          }"  
        | "tyeval (Ref e) = do {
            t \<leftarrow> tyeval_l e;
            Some (TPtr t)
          }"  
        | "tyeval (Index e1 e2) = do {
            t1\<leftarrow>tyeval e1;
            tyeval e2 \<guillemotright>= assert_int;
            case t1 of TPtr t \<Rightarrow> Some t | _ \<Rightarrow> None
          }"  
          
      
        | "tyeval_l (Derefl e) = do {
            t \<leftarrow> tyeval e;
            case t of
              TPtr t \<Rightarrow> Some t
            | _ \<Rightarrow> None
          }"
      
        | "tyeval_l (Indexl e1 e2) = do {
            t1\<leftarrow>tyeval e1;
            tyeval e2 \<guillemotright>= assert_int;
            case t1 of TPtr t \<Rightarrow> Some t | _ \<Rightarrow> None
          }"  
    end      

    definition "args_compat fd args \<equiv> do {
      argst \<leftarrow> o_map tyeval args;
      assert (map fst (fun_decl.params fd) = argst)
      }"
      
    definition "fun_compatv f args \<equiv> do {
      fdecl \<leftarrow> proc_table f;
      args_compat fdecl args
    }"  
  
    definition "fun_compat x f args \<equiv> do {
      t \<leftarrow> read_varty x;
      fdecl \<leftarrow> proc_table f;
      args_compat fdecl args;
      assert (fun_decl.rtype fdecl = Some t)
    }"  
  
    definition "fun_compatl le f args \<equiv> do {
      t \<leftarrow> tyeval_l le;
      fdecl \<leftarrow> proc_table f;
      args_compat fdecl args;
      assert (fun_decl.rtype fdecl = Some t)
    }"  
  
  
    fun tycheck_com :: "com \<rightharpoonup> unit" where
      "tycheck_com SKIP = Some ()"
    | "tycheck_com (Assignl e1 e2) = do {
        t1 \<leftarrow> tyeval_l e1;
        t2 \<leftarrow> tyeval e2;
        assert (t1=t2)
      }"  
    | "tycheck_com (Assign x e) = do {
        t1 \<leftarrow> read_varty x;
        t2 \<leftarrow> tyeval e;
        assert (t1=t2)
      }"  
    | "tycheck_com (Seq c1 c2) = tycheck_com c1 \<guillemotright> tycheck_com c2"  
    | "tycheck_com (If e c1 c2) = do {
        tyeval e \<guillemotright>= assert_int;
        tycheck_com c1;
        tycheck_com c2
      }"
    | "tycheck_com (While e c) = do {
        tyeval e \<guillemotright>= assert_int;
        tycheck_com c
      }"  
    | "tycheck_com (Free e) = do {
        tyeval e \<guillemotright>= assert_ptr
      }"  
    | "tycheck_com (Return e) = do {
        t \<leftarrow> tyeval e;
        assert (RT = Some t)
      }"  
    | "tycheck_com (Returnv) = assert (RT=None)"
    | "tycheck_com (Callfunl e f args) = fun_compatl e f args"
    | "tycheck_com (Callfun x f args) = fun_compat x f args"  
    | "tycheck_com (Callfunv f args) = fun_compatv f args"

    fun tm_com_ret :: "com \<Rightarrow> bool" where
      "tm_com_ret SKIP \<longleftrightarrow> RT=None"
    | "tm_com_ret (Assignl _ _) \<longleftrightarrow> RT=None"  
    | "tm_com_ret (Assign _ _) \<longleftrightarrow> RT=None"
    | "tm_com_ret (Seq _ c2) \<longleftrightarrow> tm_com_ret c2"
    | "tm_com_ret (If _ c1 c2) \<longleftrightarrow> tm_com_ret c1 \<and> tm_com_ret c2"
    | "tm_com_ret (While _ _) \<longleftrightarrow> RT=None"
    | "tm_com_ret (Free _) \<longleftrightarrow> RT=None"
    | "tm_com_ret (Return _) \<longleftrightarrow> True"
    | "tm_com_ret (Returnv) \<longleftrightarrow> True"
    | "tm_com_ret (Callfunl _ _ _) \<longleftrightarrow> RT=None"
    | "tm_com_ret (Callfun _ _ _) \<longleftrightarrow> RT=None"
    | "tm_com_ret (Callfunv _ _) \<longleftrightarrow> RT=None"

    abbreviation "tm_com com \<equiv> o2b (tycheck_com com) \<and> tm_com_ret com"

    
  end

  definition tm_fdecl :: "fun_decl \<Rightarrow> bool" where
    "tm_fdecl fdecl \<equiv> tm_com fdecl (fun_decl.body fdecl)"

  definition "tm_prog \<equiv> \<forall>fdecl\<in>set (program.procs p). tm_fdecl fdecl"

  definition "wt_prog \<equiv> valid_program p \<and> tm_prog"
end

locale well_typed_program = valid_program +
  assumes tm: "tm_prog"
begin

  lemma valid_fun_bodyI: 
    assumes "proc_table f = Some fd"  
    shows "tm_com fd (fun_decl.body fd)"
    using assms tm
    unfolding tm_prog_def tm_fdecl_def proc_table_of_def
    using map_of_SomeD by fastforce


end


end
