theory DivTest
imports Div
begin

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"

setup \<open>generate_c_test_code @{code test} "../TestC" "div_test"\<close>

end
