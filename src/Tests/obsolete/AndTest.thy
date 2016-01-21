theory AndTest
imports And "../Semantics/Test_Harness"
begin

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "and_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code and_test} "../TestC" "and_test"\<close>

end
