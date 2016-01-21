theory Type
imports "../Lib/Chloe_Base"
begin
  type_synonym mname = string -- \<open>Member name\<close>
  type_synonym sname = string -- \<open>Structure name\<close>

  text \<open>
    We only have one integer type. 
    We have special cases for @{text "void*"} and for pointers to structs,
    which only reference a struct name.
    The latter is required as types may be cyclic over pointers to structs. 
    \<close>

  datatype ty = 
    Null                              -- \<open>Type of null pointer @{text "void *"}\<close>
  | I                                 -- \<open>Integer type\<close>    
  | Ptr ty                            -- \<open>Pointer to type\<close>
  | StructPtr sname                   -- \<open>Pointer to struct type\<close>  
  | is_Array: Array nat ty            -- \<open>Complete array type @{text "T[N]"}\<close>
  | Struct sname "(mname \<times> ty) list"  -- \<open>Structure type\<close>
  hide_const (open) Null I Ptr StructPtr Array Struct
  
  type_synonym mdecl = "mname \<times> ty" -- \<open>Declaration of structure members\<close>
  
  type_synonym struct_map = "sname \<rightharpoonup> mdecl list" -- \<open>Resolution map for struct names\<close>

end
