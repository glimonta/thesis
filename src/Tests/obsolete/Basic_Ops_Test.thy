theory Basic_Ops_Test
imports Basic_Ops
begin


definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "basic_ops_test"\<close>

end
