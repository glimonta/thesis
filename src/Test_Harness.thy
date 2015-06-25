theory Test_Harness
imports SmallStep Pretty 
begin

section \<open>Test Harness\<close>

  datatype test_instr = 
    Discover string nat
  | Assert_Eq string int_val   
  | Assert_Eq_Null string
  | Assert_Eq_Ptr string nat

  fun adjust_addr :: "int \<Rightarrow> string \<Rightarrow> string" 
    -- \<open>Adjust address to beginning of its block\<close>
    where
    "adjust_addr ofs ca = shows_binop (shows ca) (''-'') (shows ofs) ''''"
  definition ofs_addr :: "int \<Rightarrow> string \<Rightarrow> string"
    where 
    "ofs_addr ofs ca = (shows ''*'' o shows_paren (shows_binop (shows ca) (''+'') (shows ofs))) ''''"

  definition base_var_name :: "nat \<Rightarrow> string" where
    "base_var_name i \<equiv> ''__test_harness_x_'' @ show i"

  term fold

  term list_size
  thm fold.simps


  partial_function (option) fold_option :: "('a \<Rightarrow> 's \<rightharpoonup> 's) \<Rightarrow> 'a list \<Rightarrow> 's \<rightharpoonup> 's" where
    "fold_option f l s = (case l of 
        [] \<Rightarrow> Some s 
      | x#xs \<Rightarrow> do {
          s \<leftarrow> f x s;
          fold_option f xs s
        })"

  lemma fold_option_simps[code,simp]:
    "fold_option f [] s = Some s"      
    "fold_option f (x#xs) s = do {
          s \<leftarrow> f x s;
          fold_option f xs s
        }"      
    by (subst fold_option.simps; simp)+


  lemma fold_option_mono[partial_function_mono]:     
  assumes [partial_function_mono]: "\<And>x \<sigma>. mono_option (\<lambda>fa. f fa x \<sigma>)"
  shows "mono_option (\<lambda>x. fold_option (f x) l \<sigma>)"
    apply (induction l arbitrary: \<sigma>)
    apply simp
    apply (tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
    apply simp
    apply (tactic \<open>Partial_Function.mono_tac @{context} 1\<close>)
    apply simp
    done

  context fixes \<mu> :: mem begin  

  partial_function (option) dfs 
    :: "nat set \<Rightarrow> addr \<Rightarrow> string \<Rightarrow> (nat set \<times> test_instr list) option"
    where
    [code]: "dfs D a ca = do {
      let (base,ofs) = a;

      case \<mu>!base of
        None \<Rightarrow> Some (D,[])
      | Some b \<Rightarrow> do {  
          let ca = adjust_addr ofs ca;
          if base \<notin> D then do {
            let D = insert base D;
            let emit = [Discover ca base];
            
            fold_option (\<lambda>i (D,emit). do {
              let i=int i;
              let cai = (ofs_addr i (base_var_name base));
              case b!!i of
                None \<Rightarrow> Some (D,emit)
              | Some (I v) \<Rightarrow> Some (D,emit @ [Assert_Eq cai v])
              | Some (NullVal) \<Rightarrow> Some (D,emit @ [Assert_Eq_Null cai] )
              | Some (A addr) \<Rightarrow> do {
                  (D,emit')\<leftarrow>dfs D addr cai;
                  Some (D,emit@emit')
                }
            })
              [0..<length b]
              (D,emit)

          } else do {
            Some (D,[Assert_Eq_Ptr ca base])
          }
        }    
    }"

  end

  definition emit_globals_tests :: "vname list \<Rightarrow> state \<rightharpoonup> (nat set \<times> test_instr list)" where
    "emit_globals_tests \<equiv> \<lambda>vnames (\<sigma>,\<gamma>,\<mu>). 
      fold_option (\<lambda>x (D,emit). do {
        case \<gamma> x of
          Some vo \<Rightarrow> do {
            let cai = x;
            case vo of
                None \<Rightarrow> Some (D,emit)
              | Some (I v) \<Rightarrow> Some (D,emit @ [Assert_Eq cai v])
              | Some (NullVal) \<Rightarrow> Some (D,emit @ [Assert_Eq_Null cai] )
              | Some (A addr) \<Rightarrow> do {
                  (D,emit')\<leftarrow>dfs \<mu> D addr cai;
                  Some (D,emit@emit')
                }
          }
        | _ \<Rightarrow> Some (D,emit)
      }
      ) vnames ({},[])"

  definition tests_variables :: "test_instr list \<Rightarrow> nat \<Rightarrow> shows" where
    "tests_variables l ind \<equiv> foldr (\<lambda>                   
      (Discover _ i) \<Rightarrow> indent_basic ind (shows dflt_type o shows '' *'' o shows (base_var_name i))
      | _ \<Rightarrow> id
      ) l"

  definition tests_instructions :: "test_instr list \<Rightarrow> nat \<Rightarrow> shows" where
    "tests_instructions l ind \<equiv> foldr (\<lambda>                   
        (Discover ca i) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_DISCOVER '' o shows_paren ( shows ca o shows '', '' o shows (base_var_name i)))
      | (Assert_Eq ca v) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_ASSERT_EQ '' o shows_paren ( shows ca o shows '', '' o shows v))
      | (Assert_Eq_Null ca) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_ASSERT_EQ_NULL '' o shows_paren ( shows ca ))
      | (Assert_Eq_Ptr ca i) \<Rightarrow> indent_basic ind (shows ''__TEST_HARNESS_ASSERT_EQ_PTR '' o shows_paren ( shows ca o shows '', '' o shows (base_var_name i)))
      ) l"

  definition init_discovered_shows :: "nat \<Rightarrow> shows" where
    "init_discovered_shows ind \<equiv> indent_basic ind (shows ''discovered = hashset_create()'')"

  definition failed_check_shows :: "string \<Rightarrow> nat \<Rightarrow> shows" where
    "failed_check_shows program_name ind \<equiv> indent ind (
      shows ''if (failed > 0)'' o shows_nl o
       (indent_basic (ind + 1) (
        shows ''printf(\"Failed %d test(s) in file '' o shows program_name o shows ''.c\", failed)''
       ))
    )"

    definition "init_disc \<equiv> init_discovered_shows 1 ''''"

    definition "failed_check p' \<equiv> failed_check_shows (program.name p') 1 ''''"

ML \<open>
  fun generate_c_test_code code vars_tests init_hash failed_check rel_path name thy =
    let 
      val code = code |> String.implode
      val vars = vars_tests |> the |> fst |> String.implode;
      val tests_code = vars_tests |> the |> snd |> String.implode;
      val init_hash = init_hash |> String.implode;
      val failed_check = failed_check |> String.implode;
      val nl = "\n";
      val str = nl ^ vars ^ nl ^ init_hash ^ nl ^ tests_code ^ nl ^ failed_check ^ nl ^ "}";
 
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
        val _ = TextIO.output (os, code);
        val _ = TextIO.flushOut os;
        val _ = TextIO.closeOut os;

        val _ = Isabelle_System.bash ("sed -i '$d ' " ^ abs_path);
      
        val os = TextIO.openAppend abs_path;
        val _ = TextIO.output (os, str);
        val _ = TextIO.flushOut os;
        val _ = TextIO.closeOut os;
      in thy end  
    end  
\<close>


end
