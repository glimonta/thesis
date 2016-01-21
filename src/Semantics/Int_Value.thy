section \<open>Integer Values\<close>
theory Int_Value
imports "~~/src/HOL/Word/Word"
begin

text \<open>We model only one fixed integer type.
  We have to assert that the result type of pointer 
  difference @{text "ptrdiff_t"} fits into this integer type.\<close>

type_synonym int_width = 64
type_synonym int_val = "int_width Word.word"

text \<open>We're using signed longs in the translation to C, this are the min, and max values that it's
  possible to represent with signed longs.
  
  Note: We are assuming 2's complement representation here. 
    This matches the @{text "intN_t"} types of C99.

\<close>

abbreviation "int_width \<equiv> len_of TYPE(int_width)"
abbreviation INT_MIN :: int where "INT_MIN \<equiv> - ((2^(int_width - 1)))"
abbreviation INT_MAX :: int where "INT_MAX \<equiv> ((2^(int_width - 1)) - 1)"


definition representable_int :: "int \<Rightarrow> bool" where
  "representable_int i \<equiv> INT_MIN \<le> i \<and> i \<le> INT_MAX"

context begin
  qualified lemma repr1: "representable_int i \<Longrightarrow> sint ((word_of_int i)::int_val) = i"
    unfolding representable_int_def
    apply (subst word_sbin.eq_norm)
    by (metis (no_types, lifting) mem_Collect_eq sints_num
      word_sbin.set_iff_norm zle_diff1_eq)
  
  qualified lemma repr2: "representable_int (sint (v::int_val))"
    unfolding representable_int_def using sint_range_size[of v]
    by (auto simp: word_size)
      
  qualified lemma repr3: "word_of_int (sint v) = v"
    by simp

end

end
