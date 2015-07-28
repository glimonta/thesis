theory Linked_List
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition linked_list_create_decl :: fun_decl
  where "linked_list_create_decl \<equiv>
    \<lparr> fun_decl.name = ''linked_list_create'',
      fun_decl.params = [],
      fun_decl.locals = [nn],
      fun_decl.body = 
        nn ::= New (Const 1);;
        (Indexl (V nn) (Const 0)) ::== Null;; (* Pointer to first element of list *)
        RETURN (V nn)
    \<rparr>"

definition get_first_decl :: fun_decl
  where "get_first_decl \<equiv>
    \<lparr> fun_decl.name = ''get_first'',
      fun_decl.params = [hh],
      fun_decl.locals = [],
      fun_decl.body = 
        RETURN (Deref (V hh))
    \<rparr>"

definition set_first_decl :: fun_decl
  where "set_first_decl \<equiv>
    \<lparr> fun_decl.name = ''set_first'',
      fun_decl.params = [hh, ff],
      fun_decl.locals = [],
      fun_decl.body = 
        (Indexl (V hh) (Const 0)) ::== V ff
    \<rparr>"

definition create_elem_decl :: fun_decl
  where "create_elem_decl \<equiv>
    \<lparr> fun_decl.name = ''create_elem'',
      fun_decl.params = [dd, nn],
      fun_decl.locals = [ee],
      fun_decl.body =
        ee ::= New (Const 2);;
        (Indexl (V ee) (Const 0)) ::== V dd;; (* Data *)
        (Indexl (V ee) (Const 1)) ::== V nn;; (* Next *)
        RETURN (V ee)
    \<rparr>"

definition get_data_decl :: fun_decl
  where "get_data_decl \<equiv>
    \<lparr> fun_decl.name = ''get_data'',
      fun_decl.params = [ee],
      fun_decl.locals = [],
      fun_decl.body = 
        RETURN (Index (V ee) (Const 0))
    \<rparr>"

definition get_next_decl :: fun_decl
  where "get_next_decl \<equiv>
    \<lparr> fun_decl.name = ''get_next'',
      fun_decl.params = [ee],
      fun_decl.locals = [],
      fun_decl.body = 
        RETURN (Index (V ee) (Const 1))
    \<rparr>"

definition set_data_decl :: fun_decl
  where "set_data_decl \<equiv>
    \<lparr> fun_decl.name = ''set_data'',
      fun_decl.params = [ee, dd],
      fun_decl.locals = [],
      fun_decl.body = 
        (Indexl (V ee) (Const 0)) ::== (V dd)
    \<rparr>"

definition set_next_decl :: fun_decl
  where "set_next_decl \<equiv>
    \<lparr> fun_decl.name = ''set_next'',
      fun_decl.params = [ee, nn],
      fun_decl.locals = [],
      fun_decl.body = 
        (Indexl (V ee) (Const 1)) ::== (V nn)
    \<rparr>"


definition linked_list_add_decl :: fun_decl
  where "linked_list_add_decl \<equiv>
    \<lparr> fun_decl.name = ''linked_list_add'',
      fun_decl.params = [hh, dd],
      fun_decl.locals = [nn, ee, ss],
      fun_decl.body = 
        nn ::= ''get_first'' ([V hh]);;
        ee ::= ''create_elem'' ([V dd, V nn]);;
        CALL ''set_first'' ([V hh, V ee])
    \<rparr>"


(* Eliminates all the occurrences of the element in the list *)
definition linked_list_delete_decl :: fun_decl
  where "linked_list_delete_decl \<equiv>
    \<lparr> fun_decl.name = ''linked_list_delete'',
      fun_decl.params = [hh, dd],
      fun_decl.locals = [nn, cc, ss, aa, pp],
      fun_decl.body = 
        nn ::= ''get_first'' ([V hh]);;
        cc ::= ''get_data'' ([V nn]);;
        (* Check if it's the first one *)
        IF (Eq (V dd) (V cc)) THEN (
          aa ::= ''get_next'' ([V nn]);;
          CALL ''set_first'' ([V hh, V aa]);;
          FREE (Derefl (V nn));;
          nn ::= V aa
        ) ELSE (
          SKIP
        );;
        pp ::= V nn;;
        WHILE (Index (V nn) (Const 1)) DO (
          nn ::= ''get_next'' ([V nn]);;
          cc ::= ''get_data'' ([V nn]);;
          IF (Eq (V dd) (V cc)) THEN (
            aa ::= ''get_next'' ([V nn]);;
            CALL ''set_next'' ([V pp, V aa]);;
            FREE (Derefl (V nn));;
            nn ::= V aa
          ) ELSE (
            SKIP
          );;
          pp ::= V nn
        )
    \<rparr>"

definition main_decl :: fun_decl
  where "main_decl \<equiv>
    \<lparr> fun_decl.name = ''main'',
      fun_decl.params = [],
      fun_decl.locals = [],
      fun_decl.body = 
        aa ::= ''linked_list_create'' ([]);;
        CALL ''linked_list_add'' ([V aa, Const 6]);;
        CALL ''linked_list_add'' ([V aa, Const 5]);;
        CALL ''linked_list_add'' ([V aa, Const 4]);;
        CALL ''linked_list_add'' ([V aa, Const 3]);;
        CALL ''linked_list_add'' ([V aa, Const 2]);;
        CALL ''linked_list_add'' ([V aa, Const 1]);;
        CALL ''linked_list_add'' ([V aa, Const 4]);;
        CALL ''linked_list_delete'' ([V aa, Const 4])
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''linked_list'',
      program.globals = [aa],
      program.procs = [linked_list_create_decl, get_first_decl, set_first_decl, create_elem_decl,
      get_data_decl, get_next_decl, set_data_decl, set_next_decl, linked_list_add_decl,
      linked_list_delete_decl, main_decl]
    \<rparr>"

definition "linked_list_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code linked_list_export}"../TestC" "linked_list"\<close>

end