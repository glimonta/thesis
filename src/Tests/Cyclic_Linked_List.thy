theory Cyclic_Linked_List
imports Test_Setup
begin

definition "mts_celem \<equiv> [(''data'',ty.I),(''next'', ty.StructPtr ''celem'')]"
definition "mts_clist \<equiv> [(''first'',ty.StructPtr ''celem'')]"

abbreviation "ty_clist \<equiv> ty.Struct ''clist'' mts_clist" 
abbreviation "ty_celem \<equiv> ty.Struct ''celem'' mts_celem" 

definition "str_celem \<equiv> \<lparr>
  struct_decl.name = ''celem'',
  struct_decl.members = mts_celem
\<rparr>"

definition "str_clist \<equiv> \<lparr>
  struct_decl.name = ''clist'',
  struct_decl.members = mts_clist
\<rparr>"

definition cyclic_linked_list_create_decl :: fun_decl
  where "cyclic_linked_list_create_decl \<equiv>
    \<lparr> fun_decl.name = ''cyclic_linked_list_create'',
      fun_decl.rtype = Some (ty.Ptr ty_clist),
      fun_decl.params = [],
      fun_decl.locals = [(nn, ty.Ptr ty_clist)],
      fun_decl.body = 
        $nn := malloc ty_clist [C 1];;
        $nn->''first'' := Null;; (* Pointer to first element of list *)
        RETURN (V nn)
    \<rparr>"

definition create_elem_decl :: fun_decl
  where "create_elem_decl \<equiv>
    \<lparr> fun_decl.name = ''create_elem'',
      fun_decl.rtype = Some (ty.Ptr ty_celem),
      fun_decl.params = [(dd, ty.I), (nn,ty.Ptr ty_celem)],
      fun_decl.locals = [(ee, ty.Ptr ty_celem)],
      fun_decl.body =
        $ee := malloc ty_celem [C 1];;
        $ee\<rightarrow>''data'' := $dd;;
        $ee\<rightarrow>''next'' := $nn;;
        RETURN (V ee)
    \<rparr>"

definition get_last_decl :: fun_decl
  where "get_last_decl \<equiv>
    \<lparr> fun_decl.name = ''get_last'',
      fun_decl.rtype = Some (ty.Ptr ty_celem),
      fun_decl.params = [(hh, ty.Ptr ty_clist)],
      fun_decl.locals = [(ff,ty.Ptr ty_celem), (nn,ty.Ptr ty_celem)],
      fun_decl.body = 
        $ff := $hh\<rightarrow>''first'';;
        $nn := $ff;;
        WHILE (!($nn\<rightarrow>''next'' == $ff)) DO (
          $nn := $nn\<rightarrow>''next''
        );;
        RETURN (V nn)
    \<rparr>"

definition cyclic_linked_list_add_decl :: fun_decl
  where "cyclic_linked_list_add_decl \<equiv>
    \<lparr> fun_decl.name = ''cyclic_linked_list_add'',
      fun_decl.rtype = None,
      fun_decl.params = [(hh,ty.Ptr ty_clist), (dd,ty.I)],
      fun_decl.locals = [(nn,ty.Ptr ty_celem), (ee,ty.Ptr ty_celem), (ll, ty.Ptr ty_celem)],
      fun_decl.body = 
        $nn := $hh\<rightarrow>''first'';;
        IF (V nn) THEN (
          $ee := ''create_elem''!([V dd, V nn]);;
          $ll := ''get_last''!([V hh]);;
          $ll\<rightarrow>''next'' := $ee;;
          $hh\<rightarrow>''first'' := $ee
        ) ELSE (
          $ee := ''create_elem''!([V dd, V nn]);;
          $ee\<rightarrow>''next'' := $ee;;
          $hh\<rightarrow>''first'' := $ee
        )
    \<rparr>"


(* Eliminates all the occurrences of the element in the list *)
definition cyclic_linked_list_delete_decl :: fun_decl
  where "cyclic_linked_list_delete_decl \<equiv>
    \<lparr> fun_decl.name = ''cyclic_linked_list_delete'',
      fun_decl.rtype = None,
      fun_decl.params = [(hh,ty.Ptr ty_clist), (dd,ty.I)],
      fun_decl.locals = [
        (pp,ty.Ptr ty_celem), (* prev *)
        (cc,ty.Ptr ty_celem), (* current *)
        (nn,ty.Ptr ty_celem) (* next *)
        ],
      fun_decl.body = (
        (* Initialize *)
        $pp := $hh\<rightarrow>''first'';;
        IF $pp THEN (
          $cc := $pp\<rightarrow>''next'';;
          $nn := $cc\<rightarrow>''next'';;
        
          (* Iterate *)
          WHILE (!($cc == $hh\<rightarrow>''first'')) DO (
            IF $cc\<rightarrow>''data'' == $dd THEN (
              $pp\<rightarrow>''next'' := $nn;;
              free $cc;;
              $cc := $nn
            ) ELSE (
              $pp := $cc;; 
              $cc := $nn
            );;
            $nn := $nn\<rightarrow>''next''
          );;

          (* Special case for first element *)
          IF $cc\<rightarrow>''data'' == $dd THEN (
            IF $cc == $nn THEN (
              (* List empty *)
              $hh\<rightarrow>''first'' := Null;;
              free $cc
            ) ELSE (
              (* List not empty *)
              $hh\<rightarrow>''first'' := $nn;;
              $pp\<rightarrow>''next'' := $nn;;
              free $cc
            )
          ) ELSE SKIP
        ) ELSE
          SKIP (* Empty list *)

      )
    \<rparr>"

definition main_decl
  where "main_decl n \<equiv>
    \<lparr> fun_decl.name = n,
      fun_decl.rtype = None,
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        $aa := ''cyclic_linked_list_create''!([]);;
        ''cyclic_linked_list_add''! ([V aa, Const 6]);;
        ''cyclic_linked_list_add''! ([V aa, Const 5]);;
        ''cyclic_linked_list_add''! ([V aa, Const 4]);;
        ''cyclic_linked_list_add''! ([V aa, Const 3]);;
        ''cyclic_linked_list_add''! ([V aa, Const 2]);;
        ''cyclic_linked_list_add''! ([V aa, Const 1]);;
        ''cyclic_linked_list_add''! ([V aa, Const 4]);;
        ''cyclic_linked_list_delete''! ([V aa, Const 4])
    \<rparr>"

definition p
  where "p n \<equiv> 
    \<lparr> program.name = ''cyclic_linked_list'',
      program.structs = [str_celem, str_clist],
      program.globals = [(aa, ty.Ptr ty_clist)],
      program.functs = [cyclic_linked_list_create_decl, create_elem_decl,
      get_last_decl,
      cyclic_linked_list_add_decl, cyclic_linked_list_delete_decl, main_decl n]
    \<rparr>"

definition "cyclic_linked_list_export \<equiv> prepare_export (p ''main'')"

definition shows_checker_err :: "'a ck \<Rightarrow> shows" where
  "shows_checker_err m \<equiv> case m of EAssert e \<Rightarrow> shows_ckerror e | _ \<Rightarrow> shows ''<Success>''"


setup \<open>export_c_code @{code cyclic_linked_list_export}"../TestC" "cyclic_linked_list"\<close>

definition p' :: program where "p' \<equiv> mk_test_prog p"
definition "test \<equiv> prepare_test_export p'"

setup \<open>generate_c_test_code @{code test} "../TestC" "cyclic_linked_list_test"\<close>


definition "pmain \<equiv> p ''main''"

definition "ces \<equiv> check_exec_shows pmain None ''''"
ML_val \<open>@{code ces} |> String.implode |> writeln\<close>

end
