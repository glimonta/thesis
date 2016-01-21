theory Test_Setup
imports "../Syntax/Pretty_Program" "../Semantics//Test_Harness"
begin

no_notation comp2 (infixl "oo" 55)

abbreviation (input) "aa \<equiv> ''a''"  abbreviation (input) "bb \<equiv> ''b''" abbreviation (input) "cc \<equiv> ''c''"
abbreviation (input) "dd \<equiv> ''d''"  abbreviation (input) "ee \<equiv> ''e''" abbreviation (input) "ff \<equiv> ''f''"
abbreviation (input) "gg \<equiv> ''g''"  abbreviation (input) "hh \<equiv> ''h''" abbreviation (input) "ii \<equiv> ''i''"
abbreviation (input) "jj \<equiv> ''j''"  abbreviation (input) "kk \<equiv> ''k''" abbreviation (input) "ll \<equiv> ''l''"
abbreviation (input) "mm \<equiv> ''m''"  abbreviation (input) "nn \<equiv> ''n''" abbreviation (input) "oo \<equiv> ''o''"
abbreviation (input) "pp \<equiv> ''p''"  abbreviation (input) "qq \<equiv> ''q''" abbreviation (input) "rr \<equiv> ''r''"
abbreviation (input) "ss \<equiv> ''s''"  abbreviation (input) "tt \<equiv> ''t''" abbreviation (input) "uu \<equiv> ''u''"
abbreviation (input) "vv \<equiv> ''v''"  abbreviation (input) "ww \<equiv> ''w''" abbreviation (input) "xx \<equiv> ''x''"
abbreviation (input) "yy \<equiv> ''y''"  abbreviation (input) "zz \<equiv> ''z''"               

abbreviation (input) "foo \<equiv> ''foo''" abbreviation (input) "bar \<equiv> ''bar''" abbreviation (input) "baz \<equiv> ''baz''"

text {* A convenient loop construct: *}

context com_syntax begin

abbreviation For :: "vname \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> com \<Rightarrow> com"
  ("(FOR _/ FROM _/ TO _/ DO _)"  [0, 0, 0, 61] 61) where
  "FOR v FROM a1 TO a2 DO c \<equiv>
     $v := a1 ;;  WHILE (Less ($v) a2) DO (c ;; $v := Plus ($v) (C 1))"

end

definition "ints vs \<equiv> map (\<lambda>x. (x,ty.I)) vs"
definition "int_ptrs vs \<equiv> map (\<lambda>x. (x,ty.Ptr ty.I)) vs"

interpretation com_syntax .

text \<open>Some attempts for compatibility with original syntax by Limonta\<close>

abbreviation (input) "Const \<equiv> C"
abbreviation (input) "Indexl \<equiv> Index"
abbreviation (input) "RETURN x \<equiv> return x"

end
