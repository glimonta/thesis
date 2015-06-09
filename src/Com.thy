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
      | is_Return: Return exp
      | Returnv (* Return for functions that return void *)
      | Callfunl lexp fname "exp list" ("_ ::== _ '(_')" [1000, 61] 61)
      | Callfun vname fname "exp list" ("_ ::= _ '(_')" [1000, 61] 61)
      | Callfunv fname "exp list" (* Call for functions that return void *)

term "''x'' ::= ''fun'' ([])"
term "(Derefl (V ''x'')) ::== ''fun'' ([])"

record fun_decl =
  name :: fname
  params :: "vname list"
  locals :: "vname list"
  body :: com

hide_const (open) name params locals body

(*fun def_returns :: "com \<Rightarrow> bool" where
  "def_returns (Return _) \<longleftrightarrow> True"
| "def_returns (c1 ;; c2) \<longleftrightarrow> def_returns c1 \<or> def_returns c2"
| "def_returns (IF _ THEN c1 ELSE c2) \<longleftrightarrow> def_returns c1 \<and> def_returns c2"
| "def_returns _ \<longleftrightarrow> False"
*)

fun valid_fun_decl :: "fun_decl \<Rightarrow> bool" 
  where "valid_fun_decl fdecl \<longleftrightarrow> 
    distinct (fun_decl.params fdecl @ fun_decl.locals fdecl)"

type_synonym global_decl = string

record program =
  name :: string
  globals :: "vname list"
  procs :: "fun_decl list"

hide_const (open) globals procs

type_synonym proc_table = "fname \<rightharpoonup> fun_decl"

definition proc_table_of :: "program \<Rightarrow> proc_table" where
  "proc_table_of p = map_of (map (\<lambda>fd. (fun_decl.name fd, fd)) (program.procs p))"

definition reserved_keywords :: "vname list" where
  "reserved_keywords =
    [''auto'', ''break'', ''case'', ''char'', ''const'', ''continue'',
     ''default'', ''do'', ''double'', ''else'', ''enum'', ''extern'',
     ''float'', ''for'', ''goto'', ''if'', ''inline'', ''int'', ''long'',
     ''register'', ''restrict'', ''return'', ''short'', ''signed'', ''sizeof'',
     ''static'', ''struct'', ''switch'', ''typedef'', ''union'', ''unsigned'',
     ''void'', ''volatile'', ''while'', ''_Bool'', ''_Complex'', ''_Imaginary'']"


fun collect_locals :: "fun_decl list \<Rightarrow> vname list" where
  "collect_locals [] = []"
| "collect_locals (p#ps) = (fun_decl.locals p) @ (collect_locals ps)"

definition valid_program :: "program \<Rightarrow> bool" 
  where "valid_program p \<equiv> 
      distinct (program.globals p)
    \<and> distinct (map fun_decl.name (program.procs p))
    \<and> (\<forall>fd\<in>set (program.procs p). valid_fun_decl fd)
    \<and> ( let
          pt = proc_table_of p
        in
         ''main'' \<in> dom pt
       \<and> fun_decl.params (the (pt ''main'')) = []
      )
    \<and> ( let
          prog_vars = set ((program.globals p) @ collect_locals (program.procs p));
          proc_names = set (map (fun_decl.name) (program.procs p))
        in
          (\<forall>name \<in> prog_vars. name \<notin> set reserved_keywords) \<and>
          (\<forall>name \<in> proc_names. name \<notin> set reserved_keywords) \<and>
          (\<forall>fname \<in> proc_names. (\<forall>vname \<in> prog_vars. fname \<noteq> vname))
      )"

context begin

private lemma dom_pt_of_alt: "dom (proc_table_of p) = set (map fun_decl.name (program.procs p))"
  unfolding proc_table_of_def 
  apply (simp add: dom_map_of_conv_image_fst)
  apply force
  done

lemma valid_program_code[code]: "valid_program p \<longleftrightarrow>
      distinct (program.globals p)
    \<and> distinct (map fun_decl.name (program.procs p))
    \<and> (\<forall>fd\<in>set (program.procs p). valid_fun_decl fd)
    \<and> ''main'' \<in> set (map fun_decl.name (program.procs p))
    \<and> (let
          pt = proc_table_of p
       in
         fun_decl.params (the (pt ''main'')) = []
      )"
  unfolding valid_program_def
  unfolding Let_def
  apply (subst dom_pt_of_alt)
  by simp
    
    
end

end

