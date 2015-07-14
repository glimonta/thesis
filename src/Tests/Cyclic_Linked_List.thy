theory Cyclic_Linked_List
imports "../SmallStep" "../Test" "../Test_Harness"
begin

definition cyclic_linked_list_create_decl :: fun_decl
  where "cyclic_linked_list_create_decl \<equiv>
    \<lparr> fun_decl.name = ''cyclic_linked_list_create'',
      fun_decl.params = [],
      fun_decl.locals = [nn],
      fun_decl.body = 
        nn ::= New (Const 1);;
        (Indexl (V nn) (Const 0)) ::== Null;; (* Pointer to first element of list *)
        Return (V nn)
    \<rparr>"

definition get_first_decl :: fun_decl
  where "get_first_decl \<equiv>
    \<lparr> fun_decl.name = ''get_first'',
      fun_decl.params = [hh],
      fun_decl.locals = [],
      fun_decl.body = 
        Return (Deref (V hh))
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
        Return (V ee)
    \<rparr>"

definition get_data_decl :: fun_decl
  where "get_data_decl \<equiv>
    \<lparr> fun_decl.name = ''get_data'',
      fun_decl.params = [ee],
      fun_decl.locals = [],
      fun_decl.body = 
        Return (Index (V ee) (Const 0))
    \<rparr>"

definition get_next_decl :: fun_decl
  where "get_next_decl \<equiv>
    \<lparr> fun_decl.name = ''get_next'',
      fun_decl.params = [ee],
      fun_decl.locals = [],
      fun_decl.body = 
        Return (Index (V ee) (Const 1))
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

definition get_last_decl :: fun_decl
  where "get_last_decl \<equiv>
    \<lparr> fun_decl.name = ''get_last'',
      fun_decl.params = [hh],
      fun_decl.locals = [ff, nn],
      fun_decl.body = 
        Callfun ff ''get_first'' [V hh];;
        nn ::= V ff;;
        WHILE (Not (Eq (Index (V nn) (Const 1)) (V ff))) DO (
          Callfun nn ''get_next'' [V nn]
        );;
        Return (V nn)
    \<rparr>"

definition cyclic_linked_list_add_decl :: fun_decl
  where "cyclic_linked_list_add_decl \<equiv>
    \<lparr> fun_decl.name = ''cyclic_linked_list_add'',
      fun_decl.params = [hh, dd],
      fun_decl.locals = [nn, ee, ss, ll],
      fun_decl.body = 
        Callfun nn ''get_first'' [V hh];;
        IF (V nn) THEN (
          Callfun ee ''create_elem'' [V dd, V nn];;
          Callfun ll ''get_last'' [V hh];;
          Callfunv ''set_next'' [V ll, V ee];;
          Callfunv ''set_first'' [V hh, V ee]
        ) ELSE (
          Callfun ee ''create_elem'' [V dd, V nn];;
          Callfunv ''set_next'' [V ee, V ee];;
          Callfunv ''set_first'' [V hh, V ee]
        )
    \<rparr>"


(* Eliminates all the occurrences of the element in the list *)
definition cyclic_linked_list_delete_decl :: fun_decl
  where "cyclic_linked_list_delete_decl \<equiv>
    \<lparr> fun_decl.name = ''cyclic_linked_list_delete'',
      fun_decl.params = [hh, dd],
      fun_decl.locals = [nn, cc, ss, aa, pp],
      fun_decl.body = 
        Callfun nn ''get_first'' [V hh];;
        Callfun cc ''get_data'' [V nn];;
        (* Check if it's the first one *)
        IF (Eq (V dd) (V cc)) THEN (
          Callfun aa ''get_next'' [V nn];;
          Callfunv ''set_first'' [V hh, V aa];;
          FREE (Derefl (V nn));;
          nn ::= V aa
        ) ELSE (
          SKIP
        );;
        pp ::= V nn;;
        WHILE (Index (V nn) (Const 1)) DO (
          Callfun nn ''get_next'' [V nn];;
          Callfun cc ''get_data'' [V nn];;
          IF (Eq (V dd) (V cc)) THEN (
            Callfun aa ''get_next'' [V nn];;
            Callfunv ''set_next'' [V pp, V aa];;
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
        Callfun aa ''cyclic_linked_list_create'' [];;
        Callfunv ''cyclic_linked_list_add'' [V aa, Const 6];;
        Callfunv ''cyclic_linked_list_add'' [V aa, Const 5];;
        Callfunv ''cyclic_linked_list_add'' [V aa, Const 4];;
        Callfunv ''cyclic_linked_list_add'' [V aa, Const 3];;
        Callfunv ''cyclic_linked_list_add'' [V aa, Const 2];;
        Callfunv ''cyclic_linked_list_add'' [V aa, Const 1];;
        Callfunv ''cyclic_linked_list_add'' [V aa, Const 4](*;;
        Callfunv ''cyclic_linked_list_delete'' [V aa, Const 4]*)
    \<rparr>"

definition p :: program
  where "p \<equiv> 
    \<lparr> program.name = ''cyclic_linked_list'',
      program.globals = [aa],
      program.procs = [cyclic_linked_list_create_decl, get_first_decl, set_first_decl, create_elem_decl,
      get_data_decl, get_next_decl, set_data_decl, set_next_decl, get_last_decl,
      cyclic_linked_list_add_decl, cyclic_linked_list_delete_decl, main_decl]
    \<rparr>"

definition "cyclic_linked_list_export \<equiv> prepare_export p"
setup \<open>export_c_code @{code cyclic_linked_list_export}"../TestC" "cyclic_linked_list"\<close>

value "execute_show [] p"

end