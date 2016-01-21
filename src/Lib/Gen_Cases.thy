theory Gen_Cases
imports Main "~~/src/HOL/Library/Monad_Syntax"
begin

  type_synonym ('a,'b,'c) GC_Clause = "('a \<rightharpoonup> 'b) \<times> ('b\<Rightarrow>'c)"

  type_synonym ('a,'b,'c) GC_Clauses = "('a,'b,'c) GC_Clause list"

  
  fun GC_Clause :: "('a,'b,'c) GC_Clause \<Rightarrow> 'a \<rightharpoonup> 'c" where
    "GC_Clause (g,f) x = do { x \<leftarrow> g x; Some (f x) }"

  fun GC_Clauses :: "('a,'b,'c) GC_Clauses \<Rightarrow> 'a \<rightharpoonup> 'c" where
    "GC_Clauses [] _ = None"
  | "GC_Clauses (c#cs) x = (
      case GC_Clause c x of 
        Some c \<Rightarrow> Some c 
      | None \<Rightarrow> GC_Clauses cs x)"  


  subsection \<open>Basic Selectors\<close>    

  abbreviation (input) "gc_id \<equiv> Some"
  abbreviation (input) "gc_nothing \<equiv> None"

  definition gc_constraint :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<rightharpoonup> 'a" where
    "gc_constraint c a \<equiv> if c a then Some a else None"

  abbreviation gc_binop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<rightharpoonup> 'a" where
    "gc_binop f y \<equiv> gc_constraint (\<lambda>x. f x y)"

  abbreviation "gc_eq \<equiv> gc_binop op ="

  subsection \<open>Selectors for standard types\<close>

  definition gc_prod :: "('a \<rightharpoonup> 'c) \<Rightarrow> ('b \<rightharpoonup> 'd) \<Rightarrow> ('a\<times>'b) \<rightharpoonup> ('c\<times>'d)"
    (infixr "\<times>\<^sub>g" 60)
  where "gc_prod C1 C2 \<equiv> \<lambda>(x,y). do {
    x \<leftarrow> C1 x;
    y \<leftarrow> C2 y;
    Some (x,y)
  }"

  primrec gc_None :: "'a option \<rightharpoonup> unit" where
    "gc_None None = Some ()"
  | "gc_None (Some _) = None"  

  primrec gc_Some :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a option \<rightharpoonup> 'b" where
    "gc_Some C None = None"
  | "gc_Some C (Some x) = C x"  


  primrec gc_Inl :: "('a \<rightharpoonup> 'c) \<Rightarrow> 'a+'x \<rightharpoonup> 'c" where
    "gc_Inl C (Inl x) = C x"
  | "gc_Inl _ (Inr _) = None"  

  primrec gc_Inr :: "('a \<rightharpoonup> 'c) \<Rightarrow> 'x+'a \<rightharpoonup> 'c" where
    "gc_Inr C (Inr x) = C x"
  | "gc_Inr _ (Inl _) = None"  

  primrec gc_Nil :: "'a list \<rightharpoonup> unit" where
    "gc_Nil Nil = Some ()"
  | "gc_Nil (_ # _) = None"  

  primrec gc_Cons :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a list \<rightharpoonup> 'c) \<Rightarrow> 'a list \<rightharpoonup> 'b\<times>'c" where
    "gc_Cons _ _ Nil = None"
  | "gc_Cons C1 C2 (x#xs) = do {
      x \<leftarrow> C1 x;
      xs \<leftarrow> C2 xs;
      Some (x,xs)
    }"  


  (* TODO: 
    How to elegantly attach constraints? 
    Simulate ML's "as" operator?
    Is there an elegant way to get rid of union's in result type?
    *)  

  term "gc_prod gc_None (gc_Some (gc_eq 7))"


end
