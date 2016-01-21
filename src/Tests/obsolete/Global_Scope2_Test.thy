theory Global_Scope2_Test
imports "Global_Scope2"
begin

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "global_scope2_test"\<close>

end
