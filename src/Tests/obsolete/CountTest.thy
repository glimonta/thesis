theory CountTest
imports "Count"
begin

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "count_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code count_test} "../TestC" "count_test"\<close>

end
