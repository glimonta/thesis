theory Compiler
imports SmallStep
begin

(* Stack Machine *)

datatype instr =
  LOADI int | LOADLOC vname | LOADADDR addr | ADD | STORE vname |
  STOREADDR addr | JMP int | JMPLESS int | JMPGE int

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config option" where
  "iexec instr (i, (\<sigma>, \<mu>), stk) = (case instr of
  LOADI n \<Rightarrow> Some (i+1, (\<sigma>, \<mu>), (I n)#stk) |
  LOADLOC x \<Rightarrow> Some (i+1, (\<sigma>, \<mu>), \<sigma> x#stk) |
  LOADADDR addr \<Rightarrow> do {
    v \<leftarrow> load addr \<mu>;
    Some (i+1, (\<sigma>, \<mu>), v#stk)
  } |
  ADD \<Rightarrow> do {
    v \<leftarrow> plus_val (hd2 stk) (hd stk);
    Some (i+1, (\<sigma>, \<mu>), v # tl2 stk)
  } |
  STORE x \<Rightarrow> Some (i+1, (\<sigma>(x := hd stk), \<mu>), tl stk) |
  STOREADDR addr \<Rightarrow> do {
    \<mu> \<leftarrow> store addr \<mu> (hd stk);
    Some (i+1, (\<sigma>, \<mu>), tl stk)
  } |
  JMP n \<Rightarrow> Some (i+1+n, (\<sigma>, \<mu>), stk) |
  JMPLESS n \<Rightarrow> do {
    v \<leftarrow> less_val (hd2 stk) (hd stk);
    Some (if truth_value_of v then i+1+n else i+1,(\<sigma>, \<mu>),tl2 stk)
  } |
  JMPGE n \<Rightarrow> do {
    v \<leftarrow> (less_val (hd2 stk) (hd stk));
    v \<leftarrow> not_val v;
    Some (if truth_value_of v then i+1+n else i+1,(\<sigma>, \<mu>),tl2 stk)
  })"

definition
  exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config option \<Rightarrow> bool"
     ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60) 
where
  "P \<turnstile> c \<rightarrow> c' = 
  (\<exists>i s stk. c = (i,s,stk) \<and> c' = iexec(P!!i) (i,s,stk) \<and> 0 \<le> i \<and> i < list_size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < list_size P
  \<Longrightarrow> P \<turnstile> (i,s,stk) \<rightarrow> c'"
by (simp add: exec1_def)

end
