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

| Assignl:     "\<lbrakk>eval_l x s = Some ((A (i,j)), s\<^sub>1); eval a s\<^sub>1 = Some (v, s\<^sub>2); update_mem (i,j) v s\<^sub>2 = s\<^sub>3\<rbrakk>
                 \<Longrightarrow> (x ::== a, s) \<rightarrow> Some (SKIP, s\<^sub>3)"
| AssignlNone: "eval a s = None \<or> eval_l x s = None \<Longrightarrow> (x ::== a, s) \<rightarrow> None"

| Seq1:    "(SKIP;; c\<^sub>2, s) \<rightarrow> Some (c\<^sub>2, s)"
| Seq2:    "(c\<^sub>1,s) \<rightarrow> Some (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> Some (c\<^sub>1';;c\<^sub>2,s')"
| SeqNone: "(c\<^sub>1,s) \<rightarrow> None \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> None"

| IfTrue:  "\<lbrakk>eval b s = Some (v, s'); v \<noteq> (I 0)\<rbrakk>
             \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>1,s')"
| IfFalse: "\<lbrakk>eval b s = Some (v, s'); v = (I 0)\<rbrakk>
             \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> Some (c\<^sub>2,s')"
| IfNone:  "eval b s = None \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> None"

| While:   "(WHILE b DO c,s) \<rightarrow> Some (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

(* Missing the free small_step, I'm not sure what it should do 
| Free: "(FREE x, s) \<rightarrow> Some (SKIP, s\<^sub>2)"
*)
| FreeNone: "eval_l x s = None \<Longrightarrow> (FREE x, s) \<rightarrow> None"

end
