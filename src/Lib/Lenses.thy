section \<open>Lenses\<close>
theory Lenses
imports Error_Monad
begin

  subsection \<open>Basic Definition\<close>
  type_synonym ('a,'b,'e) elens = "('a \<Rightarrow> ('b,'e) error) \<times> ('b \<Rightarrow> 'a \<Rightarrow> ('a,'e) error)"  

  primrec eget :: "('a,'b,'e) elens \<Rightarrow> 'a \<Rightarrow> ('b,'e) error" where "eget (g,s) = g"
  primrec eset :: "('a,'b,'e) elens \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> ('a,'e) error" where "eset (g,s) = s"

  (* TODO: The behaviour in case of error is not specified here *)
  locale elens = 
    fixes l :: "('a,'b,'e) elens"
    assumes get_set[e_vcg]: "e_spec (op = b) (\<lambda>_. True) True (eset l b a \<bind> eget l)"
    assumes set_get[e_vcg]: "e_spec (op = a) (\<lambda>_. True) True (do { b \<leftarrow> eget l a; eset l b a })"
    assumes get_term[simp]: "\<not>is_nonterm (eget l a)"
    assumes set_term[simp]: "\<not>is_nonterm (eset l b a)"
    (*assumes set_set[simp]: "eset l b a \<bind> eset l b = eset l b a"*)

  definition ecompose :: "('a,'b,'e) elens \<Rightarrow> ('b,'c,'e) elens \<Rightarrow> ('a,'c,'e) elens" (infixl "o\<^sub>l" 55)
  where
    "ecompose \<equiv> \<lambda>l1 l2. ( \<lambda>a. eget l1 a \<bind> eget l2, \<lambda>c a. do { b \<leftarrow> eget l1 a; b \<leftarrow> eset l2 c b; eset l1 b a })"

  notation ecompose (infixl "\<circ>\<^sub>l" 55)  

  lemma elens_compose[simp]:
    assumes "elens l1"  
    assumes "elens l2"  
    shows "elens (ecompose l1 l2)"
  proof -
    interpret l1: elens l1 by fact
    interpret l2: elens l2 by fact
  
    show ?thesis
      apply unfold_locales
      using l1.get_set l2.get_set 
      apply (simp add: ecompose_def pw_espec_iff; blast)

      using l1.set_get l2.set_get 
      apply (simp add: ecompose_def pw_espec_iff)
      apply safe 
      apply (metis is_res.elims(2) is_res.simps(1))
      apply (simp add: ecompose_def pw_espec_iff)
      apply (simp add: ecompose_def pw_espec_iff)
      done
  qed    

  lemma e_vcg_e_compose_get[e_vcg]:
    assumes [e_vcg]: "e_spec P1 E1 T1 (eget l1 a)"
    assumes [e_vcg]: "\<And>b. P1 b \<Longrightarrow> e_spec (P2 b) (E2 b) (T2 b) (eget l2 b)"
    shows "e_spec 
      (\<lambda>c. \<exists>b. P1 b \<and> P2 b c) 
      (\<lambda>e. E1 e \<or> (\<exists>b. P1 b \<and> E2 b e)) 
      (T1 \<or> (\<exists>b. P1 b \<and> T2 b)) 
      (eget (l1 o\<^sub>l l2) a)"
    unfolding ecompose_def
    by e_vcg
  
  
  lemma e_vcg_e_compose_set[e_vcg]:
    assumes [e_vcg]: "e_spec P1 E1 T1 (eget l1 a)"
    assumes [e_vcg]: "\<And>b. P1 b \<Longrightarrow> e_spec (P2 b) (E2 b) (T2 b) (eset l2 c b)"
    assumes [e_vcg]: "\<And>b c. \<lbrakk>P1 b; P2 b c\<rbrakk> \<Longrightarrow> e_spec (P3 b c) (E3 b c) (T3 b c) (eset l1 c a)"
    shows "e_spec 
      (\<lambda>a. \<exists>b c. P1 b \<and> P2 b c \<and> P3 b c a) 
      (\<lambda>e. E1 e \<or> (\<exists>b. P1 b \<and> (E2 b e \<or> (\<exists>c. P2 b c \<and> E3 b c e)))) 
      (T1 \<or> (\<exists>b. P1 b \<and> (T2 b \<or> (\<exists>c. P2 b c \<and> T3 b c))))
      (eset (l1 o\<^sub>l l2) c a)"
    unfolding ecompose_def
    by e_vcg

  lemma ecompose_assoc:
    "a o\<^sub>l (b o\<^sub>l c) = (a o\<^sub>l b) o\<^sub>l c"
    unfolding ecompose_def
    apply (auto )
    oops (* TODO: Spec of elens not yet adequate for error-case ?*)
  


  lemmas [simp, intro!] = elens.get_term elens.set_term


  subsection \<open>Basic Lenses\<close>
  definition l_id :: "('a,'a,_) elens" where "l_id \<equiv> (return, \<lambda>a _. return a)"

  lemma elens_id[simp]: "elens (l_id)"
    unfolding l_id_def
    by (unfold_locales) e_vcg+

  lemma l_id_get_spec[e_vcg]: "e_spec (op = a) (\<lambda>_. False) (False) (eget l_id a)"  
    unfolding l_id_def by e_vcg

  lemma l_id_set_spec[e_vcg]: "e_spec (op = a) (\<lambda>_. False) (False) (eset l_id a foo)"  
    unfolding l_id_def by e_vcg

  definition l_fail :: "'e \<Rightarrow> ('a,'b,'e) elens" where "l_fail e \<equiv> (\<lambda>_. EAssert e, \<lambda>_ _. EAssert e)"  
    
  lemma elens_fail[simp]: "elens (l_fail e)"
    unfolding l_fail_def
    by (unfold_locales) e_vcg+

  subsection \<open>Generic Lenses\<close>
  text \<open>Generic lens to access one-argument constructors\<close>  

  context
    fixes isC :: "'a \<Rightarrow> bool"
    and theC :: "'a \<Rightarrow> 'b"
    and C :: "'b \<Rightarrow> 'a"
    and e :: "'e"
  begin
    -- \<open>This indirection is required for code generation to work properly. (sigh)\<close>
    definition "l_C1_lens \<equiv> (
      \<lambda>a. if isC a then return (theC a) else EAssert e,
      \<lambda>b a. if isC a then return (C b) else EAssert e
    )"
  end  

  locale l_C1 =
    fixes isC :: "'a \<Rightarrow> bool"
    and theC :: "'a \<Rightarrow> 'b"
    and C :: "'b \<Rightarrow> 'a"
    and e :: "'e"
    assumes [simp]: "\<And>x. theC (C x) = x"
    assumes [simp]: "\<And>x. isC x \<Longrightarrow> C (theC x) = x"
  begin
    abbreviation "l \<equiv> l_C1_lens isC theC C e"
    lemmas l_def = l_C1_lens_def[of isC theC C e]
  
    lemma
      is_elens[simp]: "elens l" and
      get_spec[e_vcg]: "e_spec (\<lambda>b. isC a \<and> b=theC a) (\<lambda>e'. e'=e \<and> \<not>isC a) False (eget l a)" and
      set_spec[e_vcg]: "e_spec (\<lambda>a'. isC a \<and> a'=C b) (\<lambda>e'. e'=e \<and> \<not>isC a) False (eset l b a)"
    apply unfold_locales
    unfolding l_def l_C1_def
    by auto
  
    lemma E: assumes "isC a" obtains b where "a=C b"
      apply (rule that[of "theC a"])
      using assms
      by auto
  
  end


  subsection \<open>Standard Lenses\<close>

  definition "l_nth e i \<equiv> (
    \<lambda>as. do { assert (i<length as) e; return (as!i) }, 
    \<lambda>a as. do { assert (i<length as) e; return (as[i:=a]) })"

  lemma elens_nth[simp]: "elens (l_nth e i)"  
    unfolding l_nth_def
    by (unfold_locales) e_vcg+

  lemma l_nth_get_spec[e_vcg]: "e_spec (\<lambda>x. l!i = x \<and> i<length l) (\<lambda>e'. e'=e \<and> \<not>(i<length l)) False (eget (l_nth e i) l)"  
    unfolding l_nth_def by e_vcg

  lemma l_nth_set_spec[e_vcg]: "e_spec (\<lambda>x. x = l[i:=b] \<and> i<length l) (\<lambda>e'. e'=e \<and> \<not>(i<length l)) False (eset (l_nth e i) b l)"  
    unfolding l_nth_def by e_vcg

  
  definition l_last :: "'e \<Rightarrow> ('a list,'a,'e) elens" where
    "l_last e \<equiv> (
      \<lambda>l. if l=[] then EAssert e else return (last l),
      \<lambda>a l. if l=[] then EAssert e else return (butlast l@[a]))"

  lemma elens_last[simp]: "elens (l_last e)"  
    unfolding l_last_def
    by (unfold_locales) e_vcg+
  
  lemma l_last_spec[e_vcg]:
    "e_spec (\<lambda>a. \<exists>l'. l=l'@[a]) (\<lambda>e'. e'=e \<and> l=[]) False (eget (l_last e) l)"
    "e_spec (\<lambda>l'. \<exists>lh ah. l=lh@[ah] \<and> l'=lh@[a]) (\<lambda>e'. e'=e \<and> l=[]) False (eset (l_last e) a l)"
    unfolding l_last_def
    by (cases l rule: rev_cases; auto)+
  
  definition l_butlast :: "'e \<Rightarrow> ('a list,'a list,'e) elens" where
    "l_butlast e \<equiv> (
      \<lambda>l. if l=[] then EAssert e else return (butlast l),
      \<lambda>a l. if l=[] then EAssert e else return (a@[last l]))"
  
  lemma elens_butlast[simp]: "elens (l_butlast e)"  
    unfolding l_butlast_def
    by (unfold_locales) e_vcg+

  lemma l_butlast_spec[e_vcg]:
    "e_spec (\<lambda>l'. \<exists>x. l=l'@[x]) (\<lambda>e'. e'=e \<and> l=[]) False (eget (l_butlast e) l)"
    "e_spec (\<lambda>l'. \<exists>lh ah. l=lh@[ah] \<and> l'=ln@[ah]) (\<lambda>e'. e'=e \<and> l=[]) False (eset (l_butlast e) ln l)"
    unfolding l_butlast_def
    by (cases l rule: rev_cases; auto)+



  definition "l_fst \<equiv> (return o fst, \<lambda>a (_,b). return (a,b))"
  lemma elens_fst[simp]: "elens l_fst"
    unfolding l_fst_def
    by (unfold_locales) e_vcg+

  lemma l_fst_get_spec[e_vcg]: "e_spec (op = (fst a)) (\<lambda>_. False) False (eget l_fst a)"  
    unfolding l_fst_def by e_vcg

  lemma l_fst_set_spec[e_vcg]: "e_spec (op = (b,snd a)) (\<lambda>_. False) False (eset l_fst b a)"  
    unfolding l_fst_def by e_vcg

  definition "l_snd \<equiv> (return o snd, \<lambda>b (a,_). return (a,b))"
  lemma elens_snd[simp]: "elens l_snd"
    unfolding l_snd_def
    by (unfold_locales) e_vcg+

  lemma l_snd_get_spec[e_vcg]: "e_spec (op = (snd a)) (\<lambda>_. False) False (eget l_snd a)"  
    unfolding l_snd_def by e_vcg

  lemma l_snd_set_spec[e_vcg]: "e_spec (op = (fst a,b)) (\<lambda>_. False) False (eset l_snd b a)"  
    unfolding l_snd_def by e_vcg

end
