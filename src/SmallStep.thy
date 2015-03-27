theory SmallStep
imports Com
begin

fun update_locs :: "vname \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "update_locs x a (\<sigma>, \<mu>) = (\<sigma>(x:=a), \<mu>)"

fun update_mem :: "addr \<Rightarrow> val \<Rightarrow> state \<Rightarrow> state" where
  "update_mem (i,j) v (\<sigma>, \<mu>) = (\<sigma>, list_update \<mu> (nat i) (list_update (\<mu> !! i) (nat j) v))"

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
| Assignl:     "\<lbrakk>eval_l x s = Some ((A (i,j)), s\<^sub>1); eval a s\<^sub>1 = Some (v, s\<^sub>2); update_mem (i,j) v s\<^sub>2 = s\<^sub>3 \<rbrakk>
                 \<Longrightarrow> (x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>3)"
| AssignlI:    "\<lbrakk>eval_l x s = Some ((I i), s')\<rbrakk> \<Longrightarrow> (x ::== a, s) \<rightarrow> None"
| AssignlNull: "\<lbrakk>eval_l x s = Some (NullVal, s')\<rbrakk> \<Longrightarrow> (x ::== a, s) \<rightarrow> None"
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


lemma
  assumes "eval_l x s = Some (v,s)"
  obtains i j where "v=A (i,j)"
  using assms
  apply (cases x)
  apply (auto split: option.splits val.splits)
done

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
    case (Some a)[simp]
    (** Your semantics has only a rule if a has the form (A (i,j),s).
      I'm trying to prove a lemma above ...*)
    thus ?thesis sorry
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
