section \<open>Control Flow Graphs\<close>
theory CFG
imports "../Syntax/Program"
begin
  text \<open>As part of our semantics, we translate programs to control flow graphs,
    to reflect the meaning of the structured control commands. 

    The nodes of the control flow graphs are commands, and the edges are 
    labeled with syntactic labels, which are interpreted in a next step. 

    Note that, by summarizing the CFG generation and interpretation of labels, 
    one gets a standard small-step semantics, which we, however, consider less
    readable than this two-step approach via a CFG.
    \<close>

  datatype effect = Basic bcom | Func fcom | Skip
  hide_const (open) Basic Func Skip

  datatype guard = Pos exp | Neg exp
  hide_const (open) Pos Neg
  
  

  datatype label = Effect effect | Guard guard
  hide_const (open) Effect Guard

  context begin interpretation com_syntax .
    abbreviation "while_unfold_node b c \<equiv> IF b THEN (c;; WHILE b DO c) ELSE SKIP"
  end

  inductive cfg :: "com \<Rightarrow> label \<Rightarrow> com \<Rightarrow> bool" where
    basic: "cfg (com.Basic c) (label.Effect (effect.Basic c)) com.Skip"
  | func: "cfg (com.Func c) (label.Effect (effect.Func c)) com.Skip"
  | seq1: "cfg (com.Seq com.Skip c) (label.Effect effect.Skip) c"  
  | seq2: "\<lbrakk> cfg c\<^sub>1 a c\<^sub>1' \<rbrakk> \<Longrightarrow> cfg (com.Seq c\<^sub>1 c\<^sub>2) a (com.Seq c\<^sub>1' c\<^sub>2)"  
  | if_true: "cfg (com.If b c\<^sub>1 c\<^sub>2) (label.Guard (guard.Pos b)) c\<^sub>1"
  | if_false: "cfg (com.If b c\<^sub>1 c\<^sub>2) (label.Guard (guard.Neg b)) c\<^sub>2"
  | while: "cfg (com.While b c) (label.Effect effect.Skip) (while_unfold_node b c)"


  subsection \<open>Functional Version of CFG\<close>
  text \<open>We also formalize a functional version of the CFG, and show it equivalent with
    the relational version. This is required for both, animating the semantics, 
    and simplifying some proofs like determinism.\<close>

  datatype edge = Effect effect com | Cond exp com com
  hide_const (open) Effect Cond

  primrec cfg_step :: "com \<Rightarrow> edge" where
    "cfg_step com.Skip = undefined"
  | "cfg_step (com.Basic c) = edge.Effect (effect.Basic c) com.Skip"  
  | "cfg_step (com.Func c) = edge.Effect (effect.Func c) com.Skip"  
  | "cfg_step (com.Seq c1 c2) = (
      if c1 = com.Skip then
        edge.Effect effect.Skip c2
      else  
       ( 
        case cfg_step c1 of
          edge.Effect a c1' \<Rightarrow> edge.Effect a (com.Seq c1' c2)
        | edge.Cond e c11' c12' \<Rightarrow> edge.Cond e (com.Seq c11' c2) (com.Seq c12' c2)
      )  
    )"
  | "cfg_step (com.If b c1 c2) = edge.Cond b c1 c2"  
  | "cfg_step (com.While b c) = edge.Effect effect.Skip (while_unfold_node b c)"  

  lemma step2cfg1:
    assumes "c\<noteq>com.Skip"
    assumes "cfg_step c = edge.Effect e c'"
    shows "cfg c (label.Effect e) c'"
    using assms
    apply (induction c arbitrary: e c')
    apply (auto intro: cfg.intros split: split_if_asm edge.splits)
    done

  lemma step2cfg2:
    assumes "c\<noteq>com.Skip"
    assumes "cfg_step c = edge.Cond e c1' c2'"
    shows "cfg c (label.Guard (guard.Pos e)) c1' \<and> cfg c ((label.Guard (guard.Neg e))) c2'"
    using assms
    apply (induction c arbitrary: e c1' c2')
    by (auto intro: cfg.intros split: edge.splits split_if_asm)
    
  lemma cfg2step:
    assumes "cfg c l c'"  
    obtains e where "c\<noteq>com.Skip" "l=label.Effect e" "cfg_step c = edge.Effect e c'"
          | c2' b where "c\<noteq>com.Skip" "l=label.Guard (guard.Pos b)" "cfg_step c = edge.Cond b c' c2'"
          | c2' b where "c\<noteq>com.Skip" "l=label.Guard (guard.Neg b)" "cfg_step c = edge.Cond b c2' c'"
    using assms      
    by induction auto
    

  subsection \<open>Meta-Theorems\<close>

  text \<open>We show that there is no label from the skip-node,
    and that each other node has exactly one or two outgoing labels,
    and if it is two outgoing labels, they are opposite guards: \<close>

  definition cfg_outgoing :: "com \<Rightarrow> (label \<times> com) set" where
    "cfg_outgoing c \<equiv> {(a,c'). cfg c a c'}"


  lemma cfg_outgoing_alt: "cfg_outgoing c = (
    if c=com.Skip then 
      {} 
    else
      (case cfg_step c of
        (edge.Effect e c') \<Rightarrow> {(label.Effect e, c')}
      | (edge.Cond e c1' c2') \<Rightarrow> {
          (label.Guard (guard.Pos e),c1'),
          (label.Guard (guard.Neg e),c2')
        }
      )  
    )"  
    by (auto simp: cfg_outgoing_def elim: cfg2step split: edge.splits
      dest: step2cfg1 step2cfg2)

  lemma skip_stuck_simp[simp]: "\<not>cfg com.Skip a c"
    by (auto elim: cfg.cases)

  lemma skip_stuck[simp]: "cfg_outgoing com.Skip = {}"
    unfolding cfg_outgoing_def by auto

  lemma cfg_outgoing_cases:
    obtains
      "c=com.Skip" "cfg_outgoing c = {}"
    | e c' where "c\<noteq>com.Skip" "cfg_outgoing c = {(label.Effect e,c')}"  
    | b c\<^sub>1' c\<^sub>2' where "c\<noteq>com.Skip" "cfg_outgoing c = 
      {(label.Guard (guard.Pos b),c\<^sub>1'), (label.Guard (guard.Neg b),c\<^sub>2')}"
    unfolding cfg_outgoing_alt
    by (fastforce split: edge.splits)      






end
