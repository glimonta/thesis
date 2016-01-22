section \<open>Miscellaneous Lemmas\<close>
theory Chloe_Misc
imports Main
begin
  (* TODO: Move to Misc/Isabelle Library*)


  definition "ID_TAG \<equiv> \<lambda>x. x"
  lemma ID_TAGI: "P \<Longrightarrow> ID_TAG P" by (simp add: ID_TAG_def)


  
  subsection \<open>Maps\<close>  
  lemma map_leD[intro?, elim]: "m \<subseteq>\<^sub>m m' \<Longrightarrow> m x = Some v \<Longrightarrow> m' x = Some v"  
    by (auto simp: map_le_def dom_def)

  declare map_le_refl[intro!]  



  subsection \<open>Lists\<close>
  fun split_common_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list \<times> 'a list)"
    -- \<open>Find longest common prefix of two lists\<close>
  where
    "split_common_prefix [] l2 = ([],[],l2)"
  | "split_common_prefix l1 [] = ([],l1,[])"
  | "split_common_prefix (a#l1) (b#l2) = (
      if a=b then
        let (prf,ra,rb) = split_common_prefix l1 l2 in (b#prf,ra,rb)
      else
        ([],a#l1,b#l2)
    )"
  
  lemma split_common_prefix_correct:
    assumes "split_common_prefix l1 l2 = (prf,r1,r2)"
    shows "l1=prf@r1" "l2=prf@r2" "r1\<noteq>[] \<and> r2\<noteq>[] \<longrightarrow> hd r1\<noteq>hd r2"
    using assms
    apply (induction l1 l2 arbitrary: "prf" r1 r2 rule: split_common_prefix.induct)
    apply (auto split: split_if_asm prod.splits)
    done




end
