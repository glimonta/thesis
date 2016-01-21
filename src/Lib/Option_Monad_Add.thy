theory Option_Monad_Add
imports "~~/src/HOL/Library/Monad_Syntax"
begin

  (* TODO: Move *)

  primrec oassert :: "bool \<Rightarrow> unit option" where
    "oassert True = Some ()" | "oassert False = None"

  lemma oassert_iff[simp]: 
    "oassert \<Phi> = Some x \<longleftrightarrow> \<Phi>"  
    "oassert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"  
    by (cases \<Phi>) auto

  fun o_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a list \<rightharpoonup> 'b list" where
    "o_map _ [] = Some []"
  | "o_map f (x#xs) = do { y \<leftarrow> f x; ys \<leftarrow> o_map f xs; Some (y#ys) }"  

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


  (* TODO: Duplicate from Quickcheck_Exhaustive.orelse *)
  definition orelse :: "'a option => 'a option => 'a option" (infixr "orelse" 55)
  where
    [code_unfold]: "x orelse y = (case x of Some x' => Some x' | None => y)"

  lemma orelse_simps[simp]: 
    "None orelse m = m"  
    "(Some x) orelse m = Some x"  
    "m orelse n = None \<longleftrightarrow> m=None \<and> n = None"
    by (auto simp: orelse_def split: option.splits)

  lemma orelse_assoc[simp]: "(a orelse b) orelse c = a orelse b orelse c"  
    by (auto simp: orelse_def split: option.split)

  lemma orelse_idem[simp]: "a orelse a = a" by (cases a) auto


  definition "FIRST l \<equiv> foldr (op orelse) l None"

  lemma FIRST_code[simp,code]:
    "FIRST [] = None"
    "FIRST (m#ms) = m orelse FIRST ms"  
    unfolding FIRST_def by auto

  primrec FIRST_map where
    "FIRST_map f [] = None"  
  | "FIRST_map f (x#xs) = f x orelse FIRST_map f xs"  

  lemma FIRST_map_deforest[code_unfold]: "FIRST (map f l) = FIRST_map f l"
    by (induction l) auto

  lemma map_add_apply: "(m++n) x = n x orelse m x"  
    by (auto simp: orelse_def split: option.split simp: map_add_def)


end
