theory Cyclic_Linked_List_Test
imports "Cyclic_Linked_List"
begin

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"

setup \<open>generate_c_test_code @{code test} "../TestC" "cyclic_linked_list_test"\<close>


end
