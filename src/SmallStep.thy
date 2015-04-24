theory SmallStep
imports 
  Com 
  "~~/src/HOL/IMP/Star"  
  "~~/src/HOL/Library/While_Combinator"
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Code_Target_Int"
  "~~/src/HOL/Library/Code_Target_Nat"
begin

  (* TODO: Should be contained in Isabelle since de0a4a76d7aa under 
    Option.bind_split{s,_asm}*)
  lemma option_bind_split: "P (Option.bind m f) 
  \<longleftrightarrow> (m = None \<longrightarrow> P None) \<and> (\<forall>v. m=Some v \<longrightarrow> P (f v))"
    by (cases m) auto

  lemma option_bind_split_asm: "P (Option.bind m f) = (\<not>(
      m=None \<and> \<not>P None 
    \<or> (\<exists>x. m=Some x \<and> \<not>P (f x))))"
    by (cases m) auto

  lemmas option_bind_splits = option_bind_split option_bind_split_asm


fun update_locs :: "vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "update_locs x a (\<sigma>, \<mu>) = (\<sigma>(x:=a), \<mu>)"

type_synonym enabled = "state \<rightharpoonup> bool"
type_synonym transformer = "state \<rightharpoonup> state"
type_synonym cfg_label = "enabled \<times> transformer"

abbreviation en_always :: enabled where "en_always \<equiv> \<lambda>_. Some True"
abbreviation tr_id :: transformer where "tr_id \<equiv> Some"

definition "tr_assign x a s \<equiv> do {
  (v,s) \<leftarrow> eval a s;
  let s = update_locs x v s;
  Some s
}"

definition tr_assignl :: "lexp \<Rightarrow> exp \<Rightarrow> transformer"
where "tr_assignl x a s \<equiv> do {
  (addr,s) \<leftarrow> eval_l x s;
  (v,(\<sigma>, \<mu>)) \<leftarrow> eval a s;
  \<mu> \<leftarrow> store addr \<mu> v;
  Some (\<sigma>, \<mu>)
}"

fun truth_value_of :: "val \<Rightarrow> bool" where
  "truth_value_of NullVal \<longleftrightarrow> False"
| "truth_value_of (I i) \<longleftrightarrow> i\<noteq>0"
| "truth_value_of (A _) \<longleftrightarrow> True"

definition en_pos :: "exp \<Rightarrow> enabled" where
  "en_pos e s \<equiv> do {
    (v,_) \<leftarrow> eval e s;
    let b = truth_value_of v;
    Some b
  }"

definition en_neg :: "exp \<Rightarrow> enabled" where
  "en_neg e s \<equiv> do {
    (v,_) \<leftarrow> eval e s;
    let b = truth_value_of v;
    Some (\<not>b)
  }"

definition tr_eval :: "exp \<Rightarrow> transformer" where
  "tr_eval e s \<equiv> do {
    (_,s) \<leftarrow> eval e s;
    Some s
  }"

definition tr_free :: "lexp \<Rightarrow> transformer" where
  "tr_free e s \<equiv> do {
    (addr, (\<sigma>, \<mu>)) \<leftarrow> eval_l e s;
    \<mu> \<leftarrow> free addr \<mu>;
    Some (\<sigma>, \<mu>)
  }"

inductive cfg :: "com \<Rightarrow> cfg_label \<Rightarrow> com \<Rightarrow> bool" where
  Assign: "cfg (x ::= a) (en_always,tr_assign x a) SKIP"
| Assignl: "cfg (x ::== a) (en_always,tr_assignl x a) SKIP"
| Seq1: "cfg (SKIP;; c\<^sub>2) (en_always, tr_id) c\<^sub>2"
| Seq2: "\<lbrakk>cfg c\<^sub>1 a c\<^sub>1'\<rbrakk> \<Longrightarrow> cfg (c\<^sub>1;; c\<^sub>2) a (c\<^sub>1';; c\<^sub>2)"
| IfTrue: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (en_pos b, tr_eval b) c\<^sub>1"
| IfFalse: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (en_neg b, tr_eval b) c\<^sub>2"
| While: "cfg (WHILE b DO c) (en_always, tr_id) (IF b THEN c;; WHILE b DO c ELSE SKIP)"
| Free: "cfg (FREE x) (en_always, tr_free x) SKIP"

(* A configuration can take a small step if there's a cfg edge between the two commands, the
   enabled returns True and the transformer successfully transforms the state into a new one.
   If the enabled does not allow for the execution to continue then it goes to None, same
   thing happens if the enabled or the transformer return None as a result.
  *)
inductive 
  small_step :: "com \<times> state \<Rightarrow> (com \<times> state) option \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
  Base: "\<lbrakk>cfg c\<^sub>1 (en, tr) c\<^sub>2; en s = Some True; tr s = Some s\<^sub>2\<rbrakk> \<Longrightarrow> (c\<^sub>1, s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
| None: "\<lbrakk>cfg c\<^sub>1 (en, tr) c\<^sub>2; en s = None \<or> tr s = None\<rbrakk> \<Longrightarrow>(c\<^sub>1, s) \<rightarrow> None"

inductive
  small_step' :: "(com \<times> state) option \<Rightarrow> (com \<times> state) option \<Rightarrow> bool" (infix "\<rightarrow>' " 55)
where
  "cs \<rightarrow> cs' \<Longrightarrow> Some cs \<rightarrow>' cs'"

abbreviation
  small_steps :: "(com \<times> state) option \<Rightarrow> (com \<times> state) option \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step' x y"

(** A sanity check. I'm trying to prove that the semantics 
  only gets stuck at SKIP. This may reveal some problems in your 
  current semantics: **)

(*lemma 
  assumes "c\<noteq>SKIP"
  shows "\<exists>x. (c,s) \<rightarrow> x"
  using assms apply (induction c)
  apply (auto intro: small_step.intros cfg.intros)
apply (metis Assignl Base not_None_eq small_step.intros(2))
apply (metis Assign Base not_None_eq small_step.intros(2))
  *)



lemma aux:
  assumes "c\<noteq>SKIP"
  shows "\<exists>x. (c,s) \<rightarrow> x"
  using assms
proof (induction c)
  case SKIP thus ?case by simp
next
  case (Assignl x a) [simp] 
  show ?case
  proof (cases "tr_assignl x a s")
    case None[simp]
      hence "(x ::== a, s) \<rightarrow> None" using small_step.None cfg.Assignl by blast
      thus ?thesis by auto
  next
    case (Some s\<^sub>2)[simp]
      hence "(x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using small_step.Base cfg.Assignl by blast
      thus ?thesis by auto
  qed
next
  case (Assign x a)
  show ?case 
  proof (cases "tr_assign x a s")
    case None[simp]
      hence "(x ::= a, s) \<rightarrow> None" using small_step.None cfg.Assign by blast
      thus ?thesis using Assign by auto
    next
    case (Some s\<^sub>2)[simp]
      hence "(x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using small_step.Base cfg.Assign by blast
      thus ?thesis using Assign by auto
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "c\<^sub>1 = SKIP")
    case True
    hence "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)" using cfg.Seq1 small_step.Base by blast
    thus ?thesis using Seq `c\<^sub>1 = SKIP` by auto
  next
    case False
    from Seq.IH(1)[OF this] obtain a where "(c\<^sub>1,s) \<rightarrow> a" ..
    thus ?thesis
    proof cases
      case (Base en tr c\<^sub>1' s\<^sub>2)
      from Seq2[OF Base(2), of c\<^sub>2] Base show ?thesis
        by (auto intro: small_step.Base)
    next    
      case (None en tr c\<^sub>1')
      from Seq2[OF None(2), of c\<^sub>2] None show ?thesis
        by (auto intro: small_step.None)
    qed
  qed
      

(*  {
    assume "c\<^sub>1 = SKIP"
    have ?case sorry
  } moreover {
    assume "c\<^sub>1 \<noteq> SKIP"
    have ?case sorry
  } ultimately show ?case by blast
*)
next
  case (If b c\<^sub>1 c\<^sub>2)
  show ?case
  proof (cases "en_pos b s")
    case None[simp]
      hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None" using cfg.IfTrue small_step.None by blast
      thus ?thesis using If by auto
  next
    case (Some a)[simp]
      show ?thesis
      proof (cases "tr_eval b s")
        case None
          hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None" using cfg.IfTrue small_step.None by blast
          thus ?thesis using If by auto
      next
        case (Some s\<^sub>2)
          show ?thesis
          proof (cases a)
            case True
              hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>1, s\<^sub>2)"
              using `en_pos b s = Some a` cfg.IfTrue small_step.Base If Some by metis
              thus ?thesis using If by auto
          next
            case False[simp]
            have "en_pos b s = Some False" by simp
            hence "en_neg b s = Some True"
              unfolding en_pos_def en_neg_def
              by (auto split: option_bind_splits)
            hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
            using `tr_eval b s = Some s\<^sub>2` cfg.IfFalse small_step.Base If Some by metis
            thus ?thesis using If by auto
          qed
      qed
  qed
next
case (While b c)
  thus ?case using small_step.Base cfg.While by blast
next
case (Free x)
  show ?case
  proof (cases "tr_free x s")
    case None
      hence "(FREE x, s) \<rightarrow> None" using cfg.Free small_step.None by blast
      thus ?thesis using Free by auto
  next
    case (Some s\<^sub>2)
      hence "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using cfg.Free small_step.Base by blast
      thus ?thesis using Free by auto
  qed
qed

lemma cfg_SKIP_stuck[simp]: "\<not> cfg SKIP a c"
  by (auto elim: cfg.cases)

lemma en_neg_by_pos: "en_neg e s = map_option (HOL.Not) (en_pos e s)"
  unfolding en_pos_def en_neg_def
  by (auto split: option_bind_splits)

lemma cfg_determ: 
  assumes "cfg c a1 c'" 
  assumes "cfg c a2 c''" 
  obtains 
      "a1=a2" "c' = c''"
    | b where "a1 = (en_pos b,tr_eval b)" "a2 = (en_neg b,tr_eval b)"
    | b where "a1 = (en_neg b,tr_eval b)" "a2 = (en_pos b,tr_eval b)"
  using assms  
  apply (induction arbitrary: c'')
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (rotate_tac )
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  apply (erule cfg.cases, auto) []
  done

lemma small_step_determ:
  assumes "(c,s) \<rightarrow> c'"
  assumes "(c,s) \<rightarrow> c''"
  shows "c'=c''"
  using assms  
  apply (cases)
  apply (erule small_step.cases)
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos) []
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos) []
  apply (erule small_step.cases)
  apply simp
  apply (erule (1) cfg_determ, auto simp: en_neg_by_pos) []
  apply simp
  done


fun fstep :: "com \<times> state \<Rightarrow> (com \<times> state) option" where
  "fstep (SKIP,s) = Some (SKIP,s)"
| "fstep (x ::= a,s) = do {
    s \<leftarrow> tr_assign x a s;
    Some (SKIP,s)
  }"
| "fstep (x ::== a,s) = do {
    s \<leftarrow> tr_assignl x a s;
    Some (SKIP,s)
  }"
| "fstep (c\<^sub>1;; c\<^sub>2, s) = do {
    (c\<^sub>1', s) \<leftarrow> fstep (c\<^sub>1, s);
    case c\<^sub>1' of
      SKIP \<Rightarrow> Some (c\<^sub>2, s) |
      _ \<Rightarrow> Some (c\<^sub>1' ;; c\<^sub>2, s)
  }"
| "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = do {
    v \<leftarrow> en_pos b s;
    s \<leftarrow> tr_eval b s;
    if v then Some (c\<^sub>1, s) else Some (c\<^sub>2, s)
  }"
| "fstep (WHILE b DO c, s) = Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
| "fstep (FREE x, s) = do {
    s \<leftarrow> tr_free x s;
    Some (SKIP, s)
  }"


lemma fstep1: "(c,s) \<rightarrow> c' \<Longrightarrow> fstep (c,s) = c'"
proof (induction c arbitrary: c')
  case SKIP
    hence False using cfg.cases small_step.cases by fastforce
    thus ?case by auto
next
  case (Assignl x a)
    thus ?case
    proof (cases "tr_assignl x a s")
    print_cases
      case None
        hence "fstep (x ::== a, s) = None" by auto
        moreover have "(x ::== a, s) \<rightarrow> None" using None cfg.Assignl small_step.None by blast
        ultimately show ?thesis using Assignl small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (x ::== a, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assignl small_step.Base by blast
        ultimately show ?thesis using Assignl small_step_determ by simp
    qed
next
  case (Assign x a)
  thus ?case
  proof (cases "tr_assign x a s")
  print_cases
    case None
      hence "fstep (x ::= a, s) = None" by auto
      moreover have "(x ::= a, s) \<rightarrow> None" using None cfg.Assign small_step.None by blast
      ultimately show ?thesis using Assign small_step_determ by simp
  next
    case (Some s\<^sub>2)
      hence "fstep (x ::= a, s) = Some (SKIP, s\<^sub>2)" by auto
      moreover have "(x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assign small_step.Base by blast
      ultimately show ?thesis using Assign small_step_determ by simp
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2)
  thus ?case
  proof (cases "c\<^sub>1 = SKIP")
    case True
      hence "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)" using cfg.Seq1 small_step.Base by blast
      moreover have "fstep (c\<^sub>1;;c\<^sub>2, s) = Some (c\<^sub>2, s)" using True by simp
      ultimately show ?thesis using True fstep.simps Seq small_step_determ by fast
  next
    case False
      obtain a where "(c\<^sub>1, s) \<rightarrow> a" using aux[OF False] by blast
      thus ?thesis
      proof cases
        case (Base en tr c\<^sub>1' s\<^sub>2)
          from Seq2[OF Base(2), of c\<^sub>2] Base
            have "(c\<^sub>1 ;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>1' ;; c\<^sub>2, s\<^sub>2)" using small_step.Base by auto
          moreover have "fstep (c\<^sub>1, s) = Some (c\<^sub>1', s\<^sub>2)" using Seq Base `(c\<^sub>1, s) \<rightarrow> a` by simp
(*          moreover have "fstep (c\<^sub>1;; c\<^sub>2, s) = Some (c\<^sub>1';; c\<^sub>2, s\<^sub>2)" *)
          ultimately show ?thesis sorry
      next
        case (None en tr c\<^sub>1')
          from Seq2[OF None(2), of c\<^sub>2] None 
            have "(c\<^sub>1 ;; c\<^sub>2, s) \<rightarrow> None" using small_step.None by auto
          moreover have "fstep (c\<^sub>1, s) = None" using Seq None `(c\<^sub>1, s) \<rightarrow> a` by simp
          moreover from fstep.simps(4) [of c\<^sub>1 c\<^sub>2 s] calculation(2) bind_lzero
            have "fstep (c\<^sub>1 ;; c\<^sub>2, s) = None" by auto
          ultimately show ?thesis using small_step_determ Seq by simp
      qed
  qed
next
  case (If b c\<^sub>1 c\<^sub>2)
  thus ?case
  proof (cases "en_pos b s")
    case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis using If small_step_determ by simp
  next
    case (Some v)
    thus ?thesis
    proof (cases "tr_eval b s")
      case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis using If small_step_determ by simp
    next
      case (Some s\<^sub>2)
      thus ?thesis
      proof (cases v)
        case True
          hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>1, s\<^sub>2)" using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>1, s\<^sub>2)"
            using Some cfg.IfTrue small_step.Base `en_pos b s = Some v` `v` by metis
          ultimately show ?thesis using If small_step_determ by simp
      next
        case False[simp]
          have "en_pos b s = Some False" using `en_pos b s = Some v` by simp
          hence "en_neg b s = Some True" using en_neg_by_pos by auto
          moreover have "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>2, s\<^sub>2)"
            using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
            using Some cfg.IfFalse small_step.Base calculation(1) by metis
          ultimately show ?thesis using If small_step_determ by simp
      qed
    qed
  qed
next
  case (While b c)
    hence "fstep (WHILE b DO c, s) = Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)" by auto
    moreover have "(WHILE b DO c, s) \<rightarrow> Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
      using cfg.While small_step.Base by blast
    ultimately show ?case using While small_step_determ by simp
next
  case (Free x)
    thus ?case
    proof (cases "tr_free x s")
      case None
        hence "fstep (FREE x, s) = None" by auto
        moreover have "(FREE x, s) \<rightarrow> None" using None cfg.Free small_step.None by blast
        ultimately show ?thesis using Free small_step_determ by simp
    next
      case (Some s\<^sub>2)
        hence "fstep (FREE x, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Free small_step.Base by blast
        ultimately show ?thesis using Free small_step_determ by simp
    qed
qed



lemma fstep2: "c\<noteq>SKIP \<Longrightarrow> (c,s) \<rightarrow> (fstep (c,s))"
proof (induction c)
  case SKIP
    thus ?case by simp
next
  case (Assignl x a)
  thus ?case
  proof (cases "tr_assignl x a s")
  print_cases
    case None
      hence "fstep (x ::== a, s) = None" by auto
      moreover have "(x ::== a, s) \<rightarrow> None" using None cfg.Assignl small_step.None by blast
      ultimately show ?thesis by auto
  next
    case (Some s\<^sub>2)
      hence "fstep (x ::== a, s) = Some (SKIP, s\<^sub>2)" by auto
      moreover have "(x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assignl small_step.Base by blast
      ultimately show ?thesis by auto
  qed
next
  case (Assign x a)
  thus ?case
  proof (cases "tr_assign x a s")
  print_cases
    case None
      hence "fstep (x ::= a, s) = None" by auto
      moreover have "(x ::= a, s) \<rightarrow> None" using None cfg.Assign small_step.None by blast
      ultimately show ?thesis by auto
  next
    case (Some s\<^sub>2)
      hence "fstep (x ::= a, s) = Some (SKIP, s\<^sub>2)" by auto
      moreover have "(x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Assign small_step.Base by blast
      ultimately show ?thesis by auto
  qed
next
  case (Seq c\<^sub>1 c\<^sub>2) 
  thus ?case
  proof (cases "c\<^sub>1 = SKIP")
    case True
      hence "fstep (SKIP;; c\<^sub>2, s) = Some (c\<^sub>2, s)" using small_step.Base cfg.Seq1 fstep1 by blast
      moreover have "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)" using cfg.Seq1 small_step.Base by blast
      ultimately show ?thesis using Seq `c\<^sub>1 = SKIP` by auto 
  next
    case False
      from Seq.IH(1)[OF this] obtain a where "(c\<^sub>1, s) \<rightarrow> a" ..
      thus ?thesis
      proof cases
        case (Base en tr c\<^sub>1' s\<^sub>2)
          from Seq2[OF Base(2), of c\<^sub>2] Base
            have "(c\<^sub>1 ;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>1' ;; c\<^sub>2, s\<^sub>2)" using small_step.Base by auto
          moreover have "fstep (c\<^sub>1 ;; c\<^sub>2, s) = Some (c\<^sub>1' ;; c\<^sub>2, s\<^sub>2)" using fstep1 calculation by blast
          ultimately show ?thesis by auto
      next    
        case (None en tr c\<^sub>1')
          from Seq2[OF None(2), of c\<^sub>2] None 
            have "(c\<^sub>1 ;; c\<^sub>2, s) \<rightarrow>None" using small_step.None by auto
          moreover have "fstep (c\<^sub>1 ;; c\<^sub>2, s) = None" using fstep1 calculation by blast
          ultimately show ?thesis by auto
      qed
  qed
next
  case (If b c\<^sub>1 c\<^sub>2)
  thus ?case
  proof (cases "en_pos b s")
    case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis by auto
  next
    case (Some v)
    thus ?thesis
    proof (cases "tr_eval b s")
      case None
      hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = None" by auto
      moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None" using None cfg.IfTrue small_step.None by blast
      ultimately show ?thesis by auto
    next
      case (Some s\<^sub>2)
      thus ?thesis
      proof (cases v)
        case True
          hence "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>1, s\<^sub>2)" using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>1, s\<^sub>2)"
            using Some cfg.IfTrue small_step.Base `en_pos b s = Some v` `v` by metis
          ultimately show ?thesis by auto
      next
        case False[simp]
          have "en_pos b s = Some False" using `en_pos b s = Some v` by simp
          hence "en_neg b s = Some True" using en_neg_by_pos by auto
          moreover have "fstep (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) = Some (c\<^sub>2, s\<^sub>2)"
            using Some `en_pos b s = Some v` by auto
          moreover have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
            using Some cfg.IfFalse small_step.Base calculation(1) by metis
          ultimately show ?thesis by auto
      qed
    qed
  qed
next
  case (While b c)
    hence "fstep (WHILE b DO c, s) = Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)" by auto
    moreover have "(WHILE b DO c, s) \<rightarrow> Some (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"
      using cfg.While small_step.Base by blast
    ultimately show ?case by auto
next
  case (Free x)
    thus ?case
    proof (cases "tr_free x s")
      case None
        hence "fstep (FREE x, s) = None" by auto
        moreover have "(FREE x, s) \<rightarrow> None" using None cfg.Free small_step.None by blast
        ultimately show ?thesis by auto
    next
      case (Some s\<^sub>2)
        hence "fstep (FREE x, s) = Some (SKIP, s\<^sub>2)" by auto
        moreover have "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using Some cfg.Free small_step.Base by blast
        ultimately show ?thesis by auto
    qed
qed
      

fun is_term :: "(com\<times>state) option \<Rightarrow> bool" where
  "is_term (Some (SKIP,_)) = True"
| "is_term None = True"
| "is_term _ = False"


definition interp :: "com \<times> state \<Rightarrow> (com\<times>state) option" where
  "interp cs \<equiv> (while 
    (HOL.Not o is_term)
    (\<lambda>Some (c,s) \<Rightarrow> fstep (c,s))
    (Some cs))"

definition "yields == \<lambda>cs cs'. Some cs \<rightarrow>* cs' \<and> is_term cs'"
definition "terminates == \<lambda>cs. \<exists>cs'. yields cs cs'"

theorem 
  assumes TERM: "terminates cs" 
  shows "(yields cs cs') \<longleftrightarrow> (cs' = interp cs)"
proof safe
  assume "yields cs cs'"
  hence a: "Some cs \<rightarrow>* cs'" and b: "is_term cs'" unfolding yields_def by auto
  show "cs' = interp cs"
(*  proof (induction arbitrary: cs')*)
  show ?thesis sorry
  thm while_unfold
  (*thm while_rule*)
next
  from TERM obtain cs' where 
    "Some cs \<rightarrow>* cs'" "is_term cs'" 
    unfolding yields_def terminates_def by auto
  have "Some cs \<rightarrow>* interp cs" "is_term (interp cs)" sorry
  thus "yields cs (interp cs)" by (auto simp: yields_def)
qed  





export_code interp in SML


end

