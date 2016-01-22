section \<open>Well-Formedness Checks\<close>
theory Wf_Checker
imports Program
begin

text \<open>This theory contains syntactic well-formedness checks,
  including:
  \begin{itemize}
    \item No keywords are used as identifiers
    \item No duplicate identifiers are declared
    \item Referenced identifiers do exist in scope (Here: Only for struct types,
        variables and functions are handled during type-checking)
    \item Types are not empty    
  \end{itemize}
\<close>

definition valid_decls :: "vname list \<Rightarrow> bool" where
  "valid_decls l \<equiv> distinct l \<and> (set l \<inter> keywords = {})"

export_code valid_decls in SML

lemma valid_decls_empty[simp]: "valid_decls []"
  by (auto simp: valid_decls_def)

lemma valid_decls_conc_conv[simp]: "valid_decls (x#ds2) \<longleftrightarrow> 
  x\<notin>keywords \<and> valid_decls ds2 \<and> (x \<notin> set ds2)"
  by (auto simp: valid_decls_def)

lemma valid_decls_append_conv[simp]: "valid_decls (ds1@ds2) \<longleftrightarrow> 
  valid_decls ds1 \<and> valid_decls ds2 \<and> (set ds1 \<inter> set ds2 = {})"
  by (auto simp: valid_decls_def)


context
  fixes SM :: struct_map
begin

  fun wf_ty :: "ty \<Rightarrow> bool" where 
    "wf_ty ty.Null \<longleftrightarrow> True"
  | "wf_ty (ty.I) \<longleftrightarrow> True"
  | "wf_ty (ty.Ptr T) \<longleftrightarrow> wf_ty T"
  | "wf_ty (ty.StructPtr sname) \<longleftrightarrow> SM sname \<noteq> None"
  | "wf_ty (ty.Array n T) \<longleftrightarrow> n>0 \<and> wf_ty T"
  | "wf_ty (ty.Struct sname mts) \<longleftrightarrow> SM sname = Some mts"

  definition wf_vdecls :: "(vname \<times> ty) list \<Rightarrow> bool" where
    "wf_vdecls l \<equiv> valid_decls (map fst l) \<and> (\<forall>ty\<in>set (map snd l). wf_ty ty)"

  lemma wf_vdecls_empty[simp]: "wf_vdecls []"
    by (auto simp: wf_vdecls_def)

  lemma wf_vdecls_conc_conv[simp]: "wf_vdecls (vd#vd2) \<longleftrightarrow> 
    wf_ty (snd vd) \<and> fst vd \<notin> keywords \<and> wf_vdecls vd2 \<and> (fst vd \<notin> fst`set vd2)"
    by (auto simp: wf_vdecls_def)

  lemma wf_vdecls_append_conv[simp]: "wf_vdecls (vd1@vd2) \<longleftrightarrow> 
    wf_vdecls vd1 \<and> wf_vdecls vd2 \<and> (fst`set vd1 \<inter> fst`set vd2 = {})"
    by (auto simp: wf_vdecls_def)




  definition wf_struct_decl :: "struct_decl \<Rightarrow> bool" where
    "wf_struct_decl sd \<equiv> wf_vdecls (struct_decl.members sd) 
      \<and> struct_decl.members sd\<noteq>[]"

  definition wf_struct_decls :: "struct_decl list \<Rightarrow> bool" where
    "wf_struct_decls sds \<equiv> 
      valid_decls (map struct_decl.name sds) 
    \<and> (\<forall>sd\<in>set sds. wf_struct_decl sd)"

  definition wf_exp :: "exp \<Rightarrow> bool" where [simp]: "wf_exp e \<equiv> True"

  fun direct_lval_exp :: "exp \<Rightarrow> bool" 
    -- \<open>Expression whose lvalue cannot be changed by side-effects.
      This is important for LHS of assignment from function's return value to be safe,
      as the order of evaluation of LHS and RHS is not specified.

      (Thanks to Robbert Krebbers for pointing me to this)

      Implemented as syntactic restriction here. 

      TODO: Prove that evaluation of such an expression does not depend on
      side-effects imposed by any function call.

      As an approximation, we can prove that evaluation does not depend on memory.
      \<close>
  where
    "direct_lval_exp (exp.E0 (op0.Var _)) \<longleftrightarrow> True"
  (*| "direct_lval_exp (exp.E1 (op1.Memb _) e) \<longleftrightarrow> direct_lval_exp e"
    TODO/FIXME: Including this requires some elaborate reasoning on a
      function call not tampering with the memory of other stack frames.
    *)
  | "direct_lval_exp _ \<longleftrightarrow> False"
    


  fun wf_com :: "com \<Rightarrow> bool" where
    "wf_com com.Skip \<longleftrightarrow> True"
  | "wf_com (com_Assign e1 e2) \<longleftrightarrow> wf_exp e1 \<and> wf_exp e2"
  | "wf_com (com.Seq c1 c2) \<longleftrightarrow> wf_com c1 \<and> wf_com c2"
  | "wf_com (com.If b c1 c2) \<longleftrightarrow> wf_exp b \<and> wf_com c1 \<and> wf_com c2"
  | "wf_com (com.While b c) \<longleftrightarrow> wf_exp b \<and> wf_com c"
  | "wf_com (com_Malloc e1 T e2) \<longleftrightarrow> wf_exp e1 \<and> wf_ty T \<and> wf_exp e2"
  | "wf_com (com_Free e) \<longleftrightarrow> wf_exp e"
  | "wf_com (com_Return e) \<longleftrightarrow> wf_exp e"
  | "wf_com (com_Returnv) \<longleftrightarrow> True"
  | "wf_com (com_Callfun e f args) \<longleftrightarrow> direct_lval_exp e \<and> wf_exp e \<and> (\<forall>e\<in>set args. wf_exp e)"  
  | "wf_com (com_Callfunv f args) \<longleftrightarrow> (\<forall>e\<in>set args. wf_exp e)"  


  definition wf_fun_decl:: "fun_decl \<Rightarrow> bool" where
    "wf_fun_decl fd \<equiv> 
      wf_vdecls (fun_decl.params fd @ fun_decl.locals fd)
    \<and> the_default True (map_option wf_ty (fun_decl.rtype fd)) 
    \<and> wf_com (fun_decl.body fd)"

  definition wf_fun_decls :: "fun_decl list \<Rightarrow> bool" where
    "wf_fun_decls fds \<equiv> valid_decls (map fun_decl.name fds)
    \<and> (\<forall>fd\<in>set fds. wf_fun_decl fd)"  

end

definition wf_program :: "program \<Rightarrow> bool" where
  "wf_program p \<equiv> let
    SM = mk_struct_map p;
    FM = mk_fun_map p
  in
    (*program.name p \<notin> keywords
  \<and>*) wf_struct_decls SM (program.structs p)  
  \<and> wf_vdecls SM (program.globals p)
  \<and> wf_fun_decls SM (program.functs p)
  \<and> FM main_fname \<noteq> None
  \<and> fun_decl.params (the (FM main_fname)) = []" 

export_code wf_program in SML

locale program_defs_loc = 
  fixes \<pi> :: program
begin
  abbreviation "SM \<equiv> mk_struct_map \<pi>"
  abbreviation "FM \<equiv> mk_fun_map \<pi>"
end

locale wf_program_loc = program_defs_loc +
  assumes WF[simp]: "wf_program \<pi>"
begin

  lemma wf_struct_decls: "wf_struct_decls SM (program.structs \<pi>)"  
    using WF by (auto simp: wf_program_def Let_def)
  lemma wf_vdecls: "wf_vdecls SM (program.globals \<pi>)"
    using WF by (auto simp: wf_program_def Let_def)
  lemma wf_fun_decls: "wf_fun_decls SM (program.functs \<pi>)"
    using WF by (auto simp: wf_program_def Let_def)

  definition "main_fd \<equiv> the (FM main_fname)"
  lemma main_exists': "FM main_fname \<noteq> None"
    using WF by (auto simp: wf_program_def Let_def)

  lemma main_exists: "FM main_fname = Some main_fd"  
    using main_exists'
    by (auto simp: main_fd_def)

  lemma main_no_param[simp]: "fun_decl.params main_fd = []"
    using WF by (auto simp: wf_program_def Let_def main_fd_def)

  lemma main_rtype[simp]: "fun_decl.rtype main = Some ty.I"  
    using WF apply (auto simp: wf_program_def Let_def main_fd_def)
    oops (* TODO/FIXME: Restrict type of main! *)


  lemma SM_ne: "SM sn = Some ms \<Longrightarrow> ms\<noteq>[]"  
    using wf_struct_decls
    by (force simp: mk_struct_map_def wf_struct_decls_def wf_struct_decl_def
      dest!: map_of_SomeD)

  lemma SM_wf_vdecls: "SM sn = Some ms \<Longrightarrow> wf_vdecls SM ms"  
    using wf_struct_decls
    by (force simp: mk_struct_map_def wf_struct_decls_def wf_struct_decl_def
      dest!: map_of_SomeD)

  lemma SM_mt_wf:
    assumes "SM sn = Some mts"
    assumes "map_of mts x = Some T"
    shows "wf_ty SM T"
    using assms SM_wf_vdecls[OF assms(1)]
    by (auto simp: wf_vdecls_def dest!: map_of_SomeD)

  lemma wf_fdeclI:
    assumes "mk_fun_map \<pi> name = Some fd"
    shows "wf_fun_decl SM fd"
    using assms WF 
    unfolding wf_program_def
    apply (auto 
      simp: mk_fun_map_def Let_def wf_fun_decls_def
      dest!: map_of_SomeD)
    done


end

fun nonzero_ty :: "ty \<Rightarrow> bool" 
  -- \<open>Types of non-zero size. These are excluded for memory allocation.\<close>
where
    "nonzero_ty ty.Null \<longleftrightarrow> True"
  | "nonzero_ty (ty.I) \<longleftrightarrow> True"
  | "nonzero_ty (ty.Ptr T) \<longleftrightarrow> nonzero_ty T"
  | "nonzero_ty (ty.StructPtr sname) \<longleftrightarrow> True"
  | "nonzero_ty (ty.Array n T) \<longleftrightarrow> n>0 \<and> nonzero_ty T"
  | "nonzero_ty (ty.Struct sname mts) \<longleftrightarrow> mts\<noteq>[] \<and> (\<forall>(_,ty)\<in>set mts. nonzero_ty ty)"

lemma nonzero_tyI:
  assumes WFP: "wf_program p"
  assumes WFT: "wf_ty (mk_struct_map p) ty" (is "wf_ty ?SM _")
  shows "nonzero_ty ty"
  using WFT
proof (induction ty rule: nonzero_ty.induct)
  case (6 sname mts) 
  hence "?SM sname = Some mts" by simp
  then obtain sd where 
    "struct_decl.name sd = sname" 
    "struct_decl.members sd = mts"
    "sd \<in> set (program.structs p)"
    unfolding mk_struct_map_def
    by (auto dest!: map_of_SomeD)
  with WFP have "mts \<noteq> []" "wf_vdecls ?SM mts"
    unfolding wf_program_def wf_struct_decls_def wf_struct_decl_def
    by (auto simp add: Let_def)
  hence "\<forall>(_,ty)\<in>set mts. nonzero_ty ty" using "6.IH"
    unfolding wf_vdecls_def
    by auto
  with \<open>mts \<noteq> []\<close> show ?case by simp
qed auto

end
