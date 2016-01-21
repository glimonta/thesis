section \<open>Integer Arithmetic\<close>
theory Arith
imports 
  "../Lib/Chloe_Base"
  Int_Value
  "../Lib/Native_Word/Word_Misc" (* For signed div and signed mod *)
begin

abbreviation assert_repr:: "int \<hookrightarrow> unit" where 
  "assert_repr i \<equiv>  assert (representable_int i) (EDynamic EOverflow)"

definition mk_repr :: "int \<hookrightarrow> int_val" where
  "mk_repr i \<equiv> do {
    assert_repr i;
    return (word_of_int i)
  }"

(*definition mk_int_val :: "int \<hookrightarrow> val" where
  "mk_int_val i = do {
    assert_repr i; 
    return (val.I (word_of_int i))
  }"*)



text \<open>Integer division with truncation towards zero, 
  conforming to the C99 standard, Sec. 6.5.5/6\<close>
definition div_towards_zero :: "int \<Rightarrow> int \<Rightarrow> int" where
  "div_towards_zero a b \<equiv> (\<bar>a\<bar> div \<bar>b\<bar>) * sgn a * sgn b"

text \<open>Integer modulo with truncation towards zero, 
  conforming to the C99 standard, Sec. 6.5.5/6\<close>
definition mod_towards_zero :: "int \<Rightarrow> int \<Rightarrow> int" where
  "mod_towards_zero a b \<equiv> a - (div_towards_zero a b) * b "

text \<open>The C99 standard, Sec. 6.5.5/6 states that "If the quotient a/b is representable,
  the expression (a/b)*b + a%b shall equal a"\<close>
lemma div_mod_conform_to_c99_aux1: 
  "div_towards_zero a b * b + mod_towards_zero a b = a"
  unfolding mod_towards_zero_def by auto
  
lemma div_mod_conform_to_c99_aux2: 
  "\<lbrakk>representable_int a; representable_int b; 
      representable_int (div_towards_zero a b)\<rbrakk> \<Longrightarrow>
    representable_int (div_towards_zero a b * b)
  \<and> representable_int (mod_towards_zero a b)
  \<and> representable_int (div_towards_zero a b * b + mod_towards_zero a b)"
  apply (simp add: div_mod_conform_to_c99_aux1)
  apply (auto simp: mod_towards_zero_def)
  apply (auto simp: representable_int_def div_towards_zero_def
    sgn_if)
  apply (smt Divides.transfer_nat_int_function_closures(1) mult_nonneg_nonneg)
  apply (smt mod_div_equality nonneg_mod_div)
  apply (smt Divides.transfer_nat_int_function_closures(1) mult_nonneg_nonpos)
  apply (smt mod_div_equality mult_minus_right nonneg_mod_div)
  apply (smt mod_div_equality nonneg_mod_div) 
  apply (smt Divides.transfer_nat_int_function_closures(1) mult_nonneg_nonneg)
  apply (smt mod_div_equality neg_mod_sign)
  apply (smt mult_nonneg_nonpos neg_imp_zdiv_neg_iff)
  apply (smt mod_div_equality nonneg_mod_div)
  apply (smt Divides.pos_mod_bound dual_order.order_iff_strict zmod_zdiv_equality')
  apply (smt mod_div_equality mult_minus_right nonneg_mod_div)
  apply (smt Divides.transfer_nat_int_function_closures(1) mult_nonneg_nonpos)
  apply (smt Divides.transfer_nat_int_function_closures(1) mult_nonneg_nonneg)
  apply (smt mod_div_equality nonneg_mod_div)
  apply (smt mult_nonneg_nonpos neg_imp_zdiv_neg_iff)
  apply (smt mod_div_equality neg_mod_sign)
  done
  

subsection \<open>Arithmetic Operations on Integers, with overflow checks\<close>

definition iop_const :: "int \<hookrightarrow> int_val" where "iop_const i \<equiv> mk_repr i"

definition iop_plus :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_plus x1 x2 \<equiv> mk_repr (sint x1 + sint x2)"

definition iop_minus :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_minus x1 x2 \<equiv> mk_repr (sint x1 - sint x2)"

definition iop_uminus :: "int_val \<hookrightarrow> int_val" where
  "iop_uminus x \<equiv> mk_repr (- sint x)"

definition iop_mult :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_mult x1 x2 \<equiv> mk_repr (sint x1 * sint x2)"

definition iop_div :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_div x1 x2 \<equiv> do {
    assert (x2\<noteq>0) (EDynamic EDivZero);
    mk_repr (div_towards_zero (sint x1) (sint x2))
  }"

definition iop_mod :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_mod x1 x2 \<equiv> do {
    assert (x2\<noteq>0) (EDynamic EDivZero);
    mk_repr (mod_towards_zero (sint x1) (sint x2))
  }"

definition b2i :: "bool \<Rightarrow> int_val" where "b2i b \<equiv> if b then 1 else 0"
definition i2b :: "int_val \<Rightarrow> bool" where "i2b i \<equiv> i\<noteq>0"

lemma [simp]: "i2b (b2i b) \<longleftrightarrow> b"
  unfolding i2b_def b2i_def by auto

definition iop_less :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_less x1 x2 \<equiv> return (b2i (x1 <s x2))"

definition iop_le :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_le x1 x2 \<equiv> return (b2i (x1 <=s x2))"

definition iop_eq :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_eq x1 x2 \<equiv> return (b2i (x1 = x2))"

definition iop_Not :: "int_val \<hookrightarrow> int_val" where
  "iop_Not x \<equiv> return (b2i (\<not>i2b x))"

definition iop_And :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_And x1 x2 \<equiv> return (b2i (i2b x1 \<and> i2b x2))"

definition iop_Or :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_Or x1 x2 \<equiv> return (b2i (i2b x1 \<or> i2b x2))"

definition iop_BNot :: "int_val \<hookrightarrow> int_val" where
  "iop_BNot x \<equiv> return (NOT x)"

definition iop_BAnd :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_BAnd x1 x2 \<equiv> return (x1 AND x2)"

definition iop_BOr :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_BOr x1 x2 \<equiv> return (x1 OR x2)"

definition iop_BXor :: "int_val \<Rightarrow> int_val \<hookrightarrow> int_val" where
  "iop_BXor x1 x2 \<equiv> return (x1 XOR x2)"

lemma div_mon_conforming: 
  assumes "iop_div a b = return c"  
  shows "do {
    v \<leftarrow> iop_mult c b;
    m \<leftarrow> iop_mod a b;
    iop_plus v m
  } = return a"
proof -
  from assms have 
    [simp]: "b\<noteq>0"
    and [simp]: "c = word_of_int (div_towards_zero (sint a) (sint b))"
    and [simp]: "representable_int (div_towards_zero (sint a) (sint b))"
    unfolding iop_div_def mk_repr_def
    by (auto simp: pw_eq_iff)
    
  have "sint c = div_towards_zero (sint a) (sint b)" 
    by (simp add: Int_Value.repr1)

  from div_mod_conform_to_c99_aux2[of "sint a" "sint b", simplified] Int_Value.repr2 have 
    "representable_int (div_towards_zero (sint a) (sint b) * sint b)"
    "representable_int (mod_towards_zero (sint a) (sint b))"
    "representable_int (div_towards_zero (sint a) (sint b) * sint b +
          mod_towards_zero (sint a) (sint b))"
    by auto
  thus ?thesis  
  by (auto simp: Int_Value.repr1 div_mod_conform_to_c99_aux1
    simp: pw_eq_iff iop_div_def iop_mult_def iop_mod_def iop_plus_def mk_repr_def)
qed


end
