theory Type
imports Main
begin
  type_synonym sname = string

  datatype type = TInt | is_TPtr: TPtr type | TNull | TStruct sname

end
