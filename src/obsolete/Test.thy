theory Test
imports Main SmallStep Pretty
begin

no_notation comp2 (infixl "oo" 55)

abbreviation "aa \<equiv> ''a''"  abbreviation "bb \<equiv> ''b''" abbreviation "cc \<equiv> ''c''"
abbreviation "dd \<equiv> ''d''"  abbreviation "ee \<equiv> ''e''" abbreviation "ff \<equiv> ''f''"
abbreviation "gg \<equiv> ''g''"  abbreviation "hh \<equiv> ''h''" abbreviation "ii \<equiv> ''i''"
abbreviation "jj \<equiv> ''j''"  abbreviation "kk \<equiv> ''k''" abbreviation "ll \<equiv> ''l''"
abbreviation "mm \<equiv> ''m''"  abbreviation "nn \<equiv> ''n''" abbreviation "oo \<equiv> ''o''"
abbreviation "pp \<equiv> ''p''"  abbreviation "qq \<equiv> ''q''" abbreviation "rr \<equiv> ''r''"
abbreviation "ss \<equiv> ''s''"  abbreviation "tt \<equiv> ''t''" abbreviation "uu \<equiv> ''u''"
abbreviation "vv \<equiv> ''v''"  abbreviation "ww \<equiv> ''w''" abbreviation "xx \<equiv> ''x''"
abbreviation "yy \<equiv> ''y''"  abbreviation "zz \<equiv> ''z''"

abbreviation "foo \<equiv> ''foo''" abbreviation "bar \<equiv> ''bar''" abbreviation "baz \<equiv> ''baz''"

text {* A convenient loop construct: *}

abbreviation For :: "vname \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> com \<Rightarrow> com"
  ("(FOR _/ FROM _/ TO _/ DO _)"  [0, 0, 0, 61] 61) where
  "FOR v FROM a1 TO a2 DO c \<equiv>
     v ::= a1 ;;  WHILE (Less (V v) a2) DO (c ;; v ::= Plus (V v) (Const (1)))"

term remdups

fun shows_error :: "chloe_error \<Rightarrow> shows" where
  "shows_error (EStatic EType) = shows ''type error''"
| "shows_error (EStatic EStructure) = shows ''structural error''"
| "shows_error (EDynamic EOverflow) = shows ''Over/underflow''"
| "shows_error (EDynamic EDivZero) = shows ''Division by zero''"
| "shows_error (EDynamic EPtr) = shows ''Invalid address''"
| "shows_error (EDynamic EUninitialized) = shows ''Uninitialized value''"
| "shows_error (EChecker EWf) = shows ''Well-formedness check failed''"
| "shows_error (EChecker ETypeChecker) = shows ''Type checker failed''"


definition "execute_show vnames p \<equiv> case execute p of
  return s \<Rightarrow> show_state (remdups (map snd (program.globals p) @ (collect_locals (program.procs p))) @ vnames) s
  | EAssert e \<Rightarrow> (shows ''<Error: '' o shows_error e o shows ''>'') ''''
  | _ \<Rightarrow> ''<Nonterm???>''"

fun is_addr :: "(nat \<times> val) \<Rightarrow> bool" where
  "is_addr (_, (A _)) = True"
| "is_addr (_, _) = False"

lemma is_addr_addr[simp]:
  assumes "is_addr (n, v)"
  shows "\<exists>addr. v = A addr"
  proof (cases v)
    case NullVal
      hence "is_addr (n, v) \<equiv> False" using is_addr_def by auto
      hence "False" using `is_addr (n,v)` by blast
      thus ?thesis by simp
  next
    case (I i)
      hence "is_addr (n, v) \<equiv> False" using is_addr_def by auto
      hence "False" using `is_addr (n,v)` by blast
      thus ?thesis by simp
  next
    case (A addr)
      thus ?thesis by simp
qed

end