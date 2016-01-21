theory BubblesortTest
imports "Bubblesort" "../Semantics/Test_Harness"
begin

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "bubblesort_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code bubblesort_test} "../TestC" "bubblesort_test"\<close>

end
