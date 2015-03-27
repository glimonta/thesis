theory SmallStep
imports Com
begin

fun update_locs :: "vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "update_locs x a (\<sigma>, \<mu>) = (\<sigma>(x:=a), \<mu>)"

fun update_mem :: "addr \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "update_mem (i,j) v (\<sigma>, \<mu>) = (\<sigma>, list_update \<mu> (nat i) (list_update (\<mu> !! i) (nat j) v))"


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
  (v,s) \<leftarrow> eval a s;
  let s = update_mem addr v s;
  Some s
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

inductive cfg :: "com \<Rightarrow> cfg_label \<Rightarrow> com \<Rightarrow> bool" where
  Assign: "cfg (x ::= a) (en_always,tr_assign x a) SKIP"
| Assignl: "cfg (x ::== a) (en_always,tr_assignl x a) SKIP"
| Seq1: "cfg (SKIP;; c\<^sub>2) (en_always, tr_id) c\<^sub>2"
| Seq2: "\<lbrakk>cfg c\<^sub>1 a c\<^sub>1'\<rbrakk> \<Longrightarrow> cfg (c\<^sub>1;; c\<^sub>2) a (c\<^sub>1';; c\<^sub>2)"
| IfTrue: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (en_pos b, tr_eval b) c\<^sub>1"
| IfFalse: "cfg (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (en_neg b, tr_eval b) c\<^sub>2"
| While: "cfg (WHILE b DO c) (en_always, tr_id) (IF b THEN c;; WHILE b DO c ELSE SKIP)"

(*
  Right now I'll add None cases to this but I'm not sure whether that's the smart choice,
  maybe there's a better way to write it I'm not aware of
*)
inductive 
  small_step :: "com \<times> state \<Rightarrow> (com \<times> state) option \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
  Assign:      "\<lbrakk>eval a s = Some (v, s\<^sub>1); update_locs x v s\<^sub>1 = s\<^sub>2\<rbrakk>
                 \<Longrightarrow> (x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)"
| AssignNone:  "eval a s = None \<Longrightarrow> (x ::= a, s) \<rightarrow> None"

(* This rules are still a bit rusty *)
| Assignl:     "\<lbrakk>eval_l x s = Some (((i,j)), s\<^sub>1); eval a s\<^sub>1 = Some (v, s\<^sub>2); update_mem (i,j) v s\<^sub>2 = s\<^sub>3 \<rbrakk>
                 \<Longrightarrow> (x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>3)"
| AssignlNone: "eval a s = None \<or> eval_l x s = None \<Longrightarrow> (x ::== a, s) \<rightarrow> None"

| Seq1:    "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)"
| Seq2:    "(c\<^sub>1,s) \<rightarrow> Some (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> Some (c\<^sub>1';;c\<^sub>2,s')"
| SeqNone: "(c\<^sub>1,s) \<rightarrow> None \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> None"

(* If the condition is anything else other than NullVall or Zero it'll take the True branch *)
| IfTrue:  "\<lbrakk>eval b s = Some (v, s'); (v \<noteq> (I 0) \<or> v \<noteq> NullVal)\<rbrakk>
             \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>1,s')"
(* If the condition is a NullVall or Zero it'll take the False branch *)
| IfFalse: "\<lbrakk>eval b s = Some (v, s'); (v = (I 0) \<or> v = NullVal)\<rbrakk>
             \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>2,s')"
| IfNone:  "eval b s = None \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None"

| While:   "(WHILE b DO c,s) \<rightarrow> Some (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

(* Missing the free small_step, I'm not sure what it should do 
| Free: "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)"
*)
| FreeNone: "eval_l x s = None \<Longrightarrow> (FREE x, s) \<rightarrow> None"


inductive_simps assignl_simp: "(x ::== a, s) \<rightarrow> cs'"
inductive_simps assign_simp: "(x ::= a, s) \<rightarrow> cs'"


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
  proof (cases "eval_l x s")
    case None[simp]
      show ?thesis 
        apply simp 
        apply (rule exI)
        apply (rule AssignlNone)
        by simp
  next
    case (Some addr_s)[simp]
    (** Your semantics has only a rule if a has the form (A (i,j),s).
      I'm trying to prove a lemma above ...*)
    show ?thesis 
    proof (cases "eval a s")
      case None[simp]
        show ?thesis 
          apply simp 
          apply (rule exI)
          apply (rule AssignlNone)
          by simp
      next  
      case Some[simp]
      

      apply (simp)
      apply (rule exI)
      apply (rule small_step.Assignl)
      apply auto

      apply (cases a) 
      
      apply (auto intro: Assignl)
qed
next
  case (Assign x a)
  show ?thesis 
  proof (cases "eval a s")
    case None[simp]
      hence "(x ::= a, s) \<rightarrow> None" using small_step.AssignNone by auto
      thus ?thesis using Assign by auto
    next
    case (Some aa)[simp]
      moreover obtain v s\<^sub>1 where "aa = (v, s\<^sub>1)" using PairE by blast
      moreover obtain s\<^sub>2 where "update_locs x v s\<^sub>1 = s\<^sub>2" by blast
      ultimately have "(x ::= a, s) \<rightarrow> Some (SKIP, s\<^sub>2)" using small_step.Assign Some by auto
      thus ?thesis using Assign by auto
  qed
next
  case (If b c1 c2)
  show ?thesis
  proof (cases "eval b s")
    case None[simp]
      hence "(IF b THEN c1 ELSE c2,s) \<rightarrow> None" using small_step.IfNone by auto
      thus ?thesis using If by auto
    next
    case (Some a)
      then obtain v s' where a: "a = (v, s')" using PairE by blast
      show ?thesis
      proof (cases v)
        case NullVal
          hence "(IF b THEN c1 ELSE c2,s) \<rightarrow> Some (c2,s')"
            using Some and a and small_step.IfFalse by auto
          thus ?thesis using If by auto
        next
        case (A x)
          hence "(IF b THEN c1 ELSE c2,s) \<rightarrow> Some (c1,s')"
            using Some and a and small_step.IfTrue by auto
          thus ?thesis using If by auto
        next
        case (I i)
          hence "i = 0 \<or> i \<noteq> 0 \<Longrightarrow> ?thesis"
          proof cases
            assume i0: "i = 0"
            hence "(IF b THEN c1 ELSE c2,s) \<rightarrow> Some (c2,s')"
              using I and i0 and `eval b s = Some a` and a and If and small_step.IfFalse by simp
            thus ?thesis using If by auto
          next
            assume i: "i \<noteq> 0"
            hence "(IF b THEN c1 ELSE c2,s) \<rightarrow> Some (c1,s')"
              using I and i and `eval b s = Some a` and a and If and small_step.IfTrue by simp
            thus ?thesis using If by auto
          qed
        thus ?thesis by auto
      qed
  qed
next
case (While b c)
  thus ?thesis using small_step.While by blast
next
case (Free x)
oops
    

end
