theory SmallStep
imports Com "~~/src/HOL/IMP/Star"
begin

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
| EnFalse: "\<lbrakk>cfg c\<^sub>1 (en, tr) c\<^sub>2; en s = Some False\<rbrakk> \<Longrightarrow>(c\<^sub>1, s) \<rightarrow> None"
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
lemma 
  assumes [simp]: "c\<noteq>SKIP"
  shows "\<exists>x. (c,s) \<rightarrow> x"
proof (cases c)
  case SKIP thus ?thesis by simp
next
  case (Assignl x a) [simp] 
  show ?thesis
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
  show ?thesis 
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
  have "c\<^sub>1 = SKIP \<or> c\<^sub>1 \<noteq> SKIP" by auto
  thus ?thesis
  proof
    assume "c\<^sub>1 = SKIP"
      hence "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)" using cfg.Seq1 small_step.Base by blast
      thus ?thesis using Seq `c\<^sub>1 = SKIP` by auto
  next
    assume "c\<^sub>1 \<noteq> SKIP"
    show ?thesis sorry
  qed
next
  case (If b c\<^sub>1 c\<^sub>2)
  show ?thesis
  proof (cases "en_pos b s")
    case None[simp]
      hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None" using cfg.IfTrue small_step.None by blast
      thus ?thesis using If by auto
  next
    case (Some a)
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
            case False
              show ?thesis
              proof (cases "en_neg b s")
                case None
                  hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None" using cfg.IfFalse small_step.None by blast
                  thus ?thesis using If by auto
              next
                case (Some c)
                  show ?thesis
                  proof (cases c)
                    case True
                      hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>2, s\<^sub>2)"
                      using `tr_eval b s = Some s\<^sub>2` cfg.IfFalse small_step.Base If Some by metis
                      thus ?thesis using If by auto
                  next
                    case False
                      hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> None"
                      using Some cfg.IfFalse small_step.EnFalse by metis
                      thus ?thesis using If by auto
                  qed
              qed
          qed
      qed
  qed
next
case (While b c)
  thus ?thesis using small_step.Base cfg.While by blast
next
case (Free x)
  show ?thesis
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

end
