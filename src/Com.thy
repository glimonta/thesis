theory Com
imports Exp
begin

type_synonym fname = string

datatype
  com = SKIP
      | Assignl lexp exp       ("_ ::== _" [1000, 61] 61)
      | Assign  vname exp      ("_ ::= _" [1000, 61] 61)
      | Seq     com  com       ("_;;/ _"  [60, 61] 60)
      | If      exp com com    ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While   exp com        ("(WHILE _/ DO _)"  [0, 61] 61)
      | Free    lexp           ("FREE _" [0])
      | Return exp
      | Callfunl lexp fname "exp list" ("_ ::== _ '(_')" [1000, 61] 61)
      | Callfun vname fname "exp list" ("_ ::= _ '(_')" [1000, 61] 61)
      | Block com

term "''x'' ::= ''fun'' ([])"
term "(Derefl (V ''x'')) ::== ''fun'' ([])"

type_synonym fun_decl = "vname list \<times> vname list \<times> com"

fun valid_fun_decl :: "fun_decl \<Rightarrow> bool" 
  where "valid_fun_decl (params,locals,com) \<longleftrightarrow> distinct (params @ locals)"

type_synonym program = "fname \<Rightarrow> fun_decl option"

definition valid_program :: "program \<Rightarrow> bool" 
  where "valid_program p \<equiv> \<forall>fd\<in>ran p. valid_fun_decl fd"


end

