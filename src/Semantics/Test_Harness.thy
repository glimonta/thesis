theory Test_Harness
imports Check_Execute "../Syntax/Pretty" "~~/src/HOL/ex/Cartouche_Examples"
begin


  fun shows_follow_subscript :: "subscript \<Rightarrow> shows" where
    "shows_follow_subscript (subscript.Idx n) = shows ''['' o shows n o shows '']''"
  | "shows_follow_subscript (subscript.Memb n) = shows ''.'' o shows n"  

  definition shows_follow_subpath :: "subpath \<Rightarrow> shows" where
    "shows_follow_subpath p = foldr shows_follow_subscript p"

  datatype test_instr = 
    Discover ty "shows" nat
  | Assert_Eq "shows" int_val   
  | Assert_Eq_Null "shows"
  | Assert_Eq_Ptr "shows" nat


  context 
    fixes \<mu> :: memory 
  begin


    definition shows_normalized_addr :: "addr \<Rightarrow> shows \<Rightarrow> shows" where
      "shows_normalized_addr \<equiv> \<lambda>(bi,p) v. do {
        (* Compute normalization offset *)
        let T = shows_ty (ty.Ptr (the (MT \<mu> bi)));
        let path = shows_follow_subpath p;
        let ofs = shows ''(char*) (&((*('' o T o shows '')0)'' o path o shows '')) - (char *)0'';
        let ofs = shows_paren ofs;
        
        (* Compute normalized address *)
        let na = shows ''('' o T o shows '')(((char*)'' o v o shows '') - '' o ofs o shows '')'';
        let na = shows_paren na;
        na
      }"

    definition shows_block_var :: "nat \<Rightarrow> shows" where "shows_block_var i \<equiv> shows ''__test_harness_x_'' o shows i"
    definition block_var_name :: "nat \<Rightarrow> string" where "block_var_name i \<equiv> shows_block_var i ''''"


    partial_function (error) check_eq :: "nat set \<Rightarrow> val \<Rightarrow> shows \<hookrightarrow> (nat set \<times> test_instr list)"  
      where "check_eq D v s = do {
        case v of
          val.Null \<Rightarrow> return (D,[Assert_Eq_Null s])
        | (val.I i) \<Rightarrow> return (D,[Assert_Eq s i])
        | (val.Addr (bi,p)) \<Rightarrow> do {
            case \<mu>!bi of
              Freed _ \<Rightarrow> return (D,[])
            | Block ty v \<Rightarrow> do { 
                let s = shows_normalized_addr (bi,p) s;
                if bi\<notin>D then do {
                  let D = insert bi D;
                  let emit1 = [Discover ty s bi];
                  let s = shows_paren (shows ''*'' o shows_block_var bi);
                  (D,emit2) \<leftarrow> check_eq D v s;
                  return (D,emit1@emit2)
                } else
                  return (D,[Assert_Eq_Ptr s bi])
              }    
          }
        | (val.Array vs) \<Rightarrow> efold (\<lambda>i (D,emit). do {
            let s' = s o shows_follow_subscript (subscript.Idx i);
            let v' = vs!i;
            (D,emit') \<leftarrow> check_eq D v' s';
            return (D,emit@emit')
          }) [0..<length vs] (D,[])
        | (val.Struct ms) \<Rightarrow> efold (\<lambda>(name,v') (D,emit). do {
            let s' = s o shows_follow_subscript (subscript.Memb name);
            (D,emit') \<leftarrow> check_eq D v' s';
            return (D,emit@emit')
          }) ms (D,[])  
        | (val.Uninit) \<Rightarrow> return (D,[])  
      }"

    declare check_eq.simps[code]  
  end    

  definition emit_tests :: "vname list \<Rightarrow> state \<hookrightarrow> (nat set \<times> test_instr list)" where
    "emit_tests vs \<equiv> \<lambda>(\<sigma>,\<gamma>,\<mu>). efold (\<lambda>x (D,emit). do {
      v \<leftarrow> eget (l_addr (the (\<gamma> x))) \<mu>;
      let s = shows x;
      (D,emit') \<leftarrow> check_eq \<mu> D v s;
      return (D,emit@emit')
    }) vs ({},[])"


  definition tests_variables :: "test_instr list \<Rightarrow> nat \<Rightarrow> shows" where
    "tests_variables l ind \<equiv> foldr (\<lambda>                   
      (Discover ty _ i) \<Rightarrow> indent_basic ind (shows_decl (block_var_name i, ty.Ptr ty))
      | _ \<Rightarrow> id
      ) l"

  definition tests_instructions :: "test_instr list \<Rightarrow> nat \<Rightarrow> shows" where
    "tests_instructions l ind \<equiv> foldr (\<lambda>                   
        (Discover ty ca i) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_DISCOVER '' o shows_paren ( ca o shows '', '' o shows_block_var i))
      | (Assert_Eq ca v) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_ASSERT_EQ '' o shows_paren ( ca o shows '', '' o shows_int_val v))
      | (Assert_Eq_Null ca) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_ASSERT_EQ_NULL '' o shows_paren ( ca ))
      | (Assert_Eq_Ptr ca i) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_ASSERT_EQ_PTR '' o shows_paren ( ca o shows '', '' o shows_block_var i))
      ) l"

  definition init_discovered_shows :: "nat \<Rightarrow> shows" where
    "init_discovered_shows ind \<equiv> indent_basic ind (shows ''__test_harness_discovered = hashset_create()'')"


  definition failed_check_shows :: "string \<Rightarrow> nat \<Rightarrow> shows" where
    "failed_check_shows program_name ind \<equiv> indent ind (
      shows ''if (__test_harness_failed > 0)'' o shows_nl o
        (indent_basic (ind + 1) (
          shows \<open>printf(\"Failed %d test(s) in file \<close> o shows program_name o shows \<open>.c (passed %d)\\n\", __test_harness_failed, __test_harness_passed)\<close>
        )) o shows_nl o
      shows ''else'' o shows_nl o  
      (indent_basic (ind + 1) (
          shows \<open>printf(\"Passed all %d test(s) in file \<close> o shows program_name o shows \<open>.c\\n\", __test_harness_passed)\<close>
        )) o shows_nl
    )"

    definition "init_disc \<equiv> init_discovered_shows 1 ''''"

    definition "failed_check p' \<equiv> failed_check_shows (program.name p') 1 ''''"


  definition prepare_test_export' :: "program \<Rightarrow> (string \<times> string) cke"
  where "prepare_test_export' prog \<equiv> do {
    code \<leftarrow> map_error Inl (prepare_export' prog);
    s \<leftarrow> check_execute prog;
    let vnames = map fst (program.globals prog);
    (_,tests) \<leftarrow> map_error Inr (emit_tests vnames s);
    let vars = tests_variables tests 1 '''';
    let instrs = tests_instructions tests 1 '''';
    let failed_check = failed_check prog;
    let init_hash = init_disc;
    let nl = ''\<newline>'';
    let test_code = nl @ vars @ nl @ init_hash @ nl @ instrs @ nl @ failed_check @ nl @ ''}'';
    return (code,test_code)
  }"
  
  (** TODO/FIXME: This way of appending test code is a DIRTY HACK! *)

  definition "prepare_test_export p \<equiv> e2o (prepare_test_export' p)"

  ML \<open>
    fun generate_c_test_code (SOME (code,test_code)) rel_path name thy =
      let 
        val code = code |> String.implode
        val test_code = test_code |> String.implode
      in
        if rel_path="" orelse name="" then
          (writeln (code ^ " <rem last line> " ^ test_code); thy)
        else let  
          val base_path = Resources.master_directory thy
          val rel_path = Path.explode rel_path
          val name_path = Path.basic name |> Path.ext "c"
        
          val abs_path = Path.appends [base_path, rel_path, name_path]
          val abs_path = Path.implode abs_path
       
          val _ = writeln ("Writing to file " ^ abs_path)
  
          val os = TextIO.openOut abs_path;
          val _ = TextIO.output (os, code);
          val _ = TextIO.flushOut os;
          val _ = TextIO.closeOut os;
  
          val _ = Isabelle_System.bash ("sed -i '$d ' " ^ abs_path);
        
          val os = TextIO.openAppend abs_path;
          val _ = TextIO.output (os, test_code);
          val _ = TextIO.flushOut os;
          val _ = TextIO.closeOut os;
        in thy end  
      end
    | generate_c_test_code NONE _ _ _ = 
        error "Invalid program or failed execution"
  
  
    fun expect_failed_test (SOME s) = error ("Expected Failed test, but got " ^ String.implode s)
      | expect_failed_test NONE = ()
  
  \<close>


  definition mk_test_prog :: "(fname \<Rightarrow> program) \<Rightarrow> program" where
    "mk_test_prog pg \<equiv> let
      p = pg ''__orig_main'';
      main = \<lparr>
        fun_decl.name = ''main'',
        fun_decl.rtype = None,
        fun_decl.params = [],
        fun_decl.locals = [],
        fun_decl.body = com_Callfunv ''__orig_main'' ([])
      \<rparr>;
      p = p\<lparr> program.functs := program.functs p @ [main]  \<rparr>
    in p"

  subsection \<open>Debugging\<close>
  
  definition "shows_err m f \<equiv> case m of 
      Error_Monad.return s \<Rightarrow> f s
    | EAssert e \<Rightarrow> shows_error e 
    | _ \<Rightarrow> shows ''<Nonterm?>''"

  definition "shows_cke m f \<equiv> case m of 
      Error_Monad.return s \<Rightarrow> f s
    | EAssert e \<Rightarrow> shows_combined_err e 
    | _ \<Rightarrow> shows ''<Nonterm?>''"

  definition "shows_ck m f \<equiv> case m of 
      Error_Monad.return s \<Rightarrow> f s
    | EAssert e \<Rightarrow> shows_ckerror e 
    | _ \<Rightarrow> shows ''<Nonterm?>''"
  
  definition "shows_eval e s \<equiv> case e of 
      None \<Rightarrow> shows ''''
    | Some e \<Rightarrow> shows_exp e o shows '' = '' o shows_err (eval_exp' s e) (shows_res' s)"
  
  definition "export_shows p \<equiv> shows_ck (prepare_export' p) shows"

  definition "\<And>n p. execn_shows (n::integer) p e \<equiv> 
    shows_err (execn (nat_of_integer n) p) (\<lambda>s. shows_state p None s o shows_nl o shows_eval e s)"

  definition "\<And>n p. check_exec_shows p e \<equiv> 
    shows_cke (check_execute p) (\<lambda>s. shows_state p None s o shows_nl o shows_eval e s)"

  (* Example:   
  ML \<open>
    @{code execn_shows} 1000 @{code p'} (SOME @{code exp1}) [] |> String.implode |> writeln
  \<close>
  *)

end
