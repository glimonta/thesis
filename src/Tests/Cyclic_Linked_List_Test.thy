theory Cyclic_Linked_List_Test
imports "Cyclic_Linked_List"
begin

definition cyclic_linked_list_main_decl :: fun_decl
  where "cyclic_linked_list_main_decl \<equiv>
    \<lparr> fun_decl.name = ''cyclic_linked_list_main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = (fun_decl.body main_decl)
    \<rparr>"

definition main_test_decl :: fun_decl
  where "main_test_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = Callfunv ''cyclic_linked_list_main'' []
    \<rparr>"

definition p' :: program
  where "p' \<equiv> 
    \<lparr> program.name = ''cyclic_linked_list_test'',
      program.globals = (program.globals p),
    program.procs = [cyclic_linked_list_create_decl, get_first_decl, set_first_decl, create_elem_decl,
      get_data_decl, get_next_decl, set_data_decl, set_next_decl, get_last_decl,
      cyclic_linked_list_add_decl, cyclic_linked_list_delete_decl, cyclic_linked_list_main_decl,
      main_test_decl]
    \<rparr>"

definition "cyclic_linked_list_test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code cyclic_linked_list_test} "../TestC" "cyclic_linked_list_test"\<close>
end