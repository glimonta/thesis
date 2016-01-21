theory Linked_List
imports Test_Setup
begin

definition 
  "ll_members \<equiv> [(''first'',ty.StructPtr ''le'')]"
definition 
  "le_members \<equiv> [(''data'',ty.I),(''next'',ty.StructPtr ''le'')]"
definition "ll_decl \<equiv> \<lparr> struct_decl.name = ''ll'', struct_decl.members = ll_members\<rparr>"
definition "le_decl \<equiv> \<lparr> struct_decl.name = ''le'', struct_decl.members = le_members\<rparr>"
abbreviation "ty_ll \<equiv> ty.Struct ''ll'' ll_members"
abbreviation "ty_le \<equiv> ty.Struct ''le'' le_members"



definition linked_list_create_decl :: fun_decl
  where "linked_list_create_decl \<equiv>
    \<lparr> fun_decl.name = ''linked_list_create'',
      fun_decl.rtype = Some (ty.Ptr ty_ll),
      fun_decl.params = [],
      fun_decl.locals = [(nn,ty.Ptr ty_ll)],
      fun_decl.body = 
        $nn := malloc ty_ll [C 1];;
        $nn\<rightarrow>''first'' := Null;;
        RETURN (V nn)
    \<rparr>"

definition linked_list_add_decl :: fun_decl
  where "linked_list_add_decl \<equiv>
    \<lparr> fun_decl.name = ''linked_list_add'',
      fun_decl.rtype = None,
      fun_decl.params = [(hh,ty.Ptr ty_ll), (dd,ty.I)],
      fun_decl.locals = [(nn,ty.Ptr ty_le), (ee,ty.Ptr ty_le)],
      fun_decl.body = 
        $nn := $hh\<rightarrow>''first'';;
        $ee := malloc ty_le [C 1];;
        $ee\<rightarrow>''data'' := $dd;;
        $ee\<rightarrow>''next'' := $nn;;
        $hh\<rightarrow>''first'' := $ee
    \<rparr>"


(* Eliminates all the occurrences of the element in the list *)
definition linked_list_delete_decl :: fun_decl
  where "linked_list_delete_decl \<equiv>
    \<lparr> fun_decl.name = ''linked_list_delete'',
      fun_decl.rtype = None,
      fun_decl.params = [(hh,ty.Ptr ty_ll), (dd,ty.I)],
      fun_decl.locals = [(pp,ty.Ptr (ty.Ptr ty_le)), (cc,ty.Ptr ty_le)],
      fun_decl.body = 
        $cc := $hh\<rightarrow>''first'';;
        $pp := &$hh\<rightarrow>''first'';;
        WHILE $cc DO (
          IF $cc\<rightarrow>''data'' == $dd THEN (
            *$pp := $cc\<rightarrow>''next'';;
            $cc := $cc\<rightarrow>''next''
          ) ELSE (
            $pp := &$cc\<rightarrow>''next'';;
            $cc := $cc\<rightarrow>''next''
          )
        )
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        com_Callfun ($aa) ''linked_list_create'' ([]);;
        com_Callfunv ''linked_list_add'' ([V aa, Const 6]);;
        com_Callfunv ''linked_list_add'' ([V aa, Const 5]);;
        com_Callfunv ''linked_list_add'' ([V aa, Const 4]);;
        com_Callfunv ''linked_list_add'' ([V aa, Const 3]);;
        com_Callfunv ''linked_list_add'' ([V aa, Const 2]);;
        com_Callfunv ''linked_list_add'' ([V aa, Const 1]);;
        com_Callfunv ''linked_list_add'' ([V aa, Const 4]);;
        com_Callfunv ''linked_list_delete'' ([V aa, Const 4])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''linked_list'',
      program.structs = [ll_decl, le_decl],
      program.globals = [(aa,ty.Ptr ty_ll)],
      program.functs = [linked_list_create_decl, linked_list_add_decl,
      linked_list_delete_decl, main_decl n]
    \<rparr>"

definition "linked_list_export \<equiv> prepare_export (p ''main'')"
setup \<open>export_c_code @{code linked_list_export}"../TestC" "linked_list"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"
setup \<open>generate_c_test_code @{code test} "../TestC" "linked_list_test"\<close>


end


