theory Memory
imports Main "~~/src/HOL/Library/AList" 
  "../Syntax/Type" Int_Value "../Syntax/Wf_Checker"
begin





subsection \<open>Lens for Valuations\<close>
  definition "l_ffld e name \<equiv> (
    \<lambda>a. case map_of a name of None \<Rightarrow> EAssert e | Some b \<Rightarrow> return b,
    \<lambda>b a. do { assert (map_of a name \<noteq> None) e; return (AList.update name b a) }
    )"

  lemma elens_ffld[simp]: "elens (l_ffld e name)"  
    unfolding l_ffld_def
    apply (unfold_locales) 
    apply (e_vcg simp: update_conv update_triv split: option.splits)+
    done
    
  lemma l_ffld_get_spec[e_vcg]: " 
    e_spec (\<lambda>x. map_of a name = Some x) (\<lambda>e'. e'=e \<and> map_of a name = None) False (eget (l_ffld e name) a)"  
    unfolding l_ffld_def by e_vcg

  lemma l_ffld_set_spec[e_vcg]: " 
    e_spec (\<lambda>a'. map_of a name \<noteq> None \<and> map_of a' = (map_of a)(name \<mapsto> b)) (\<lambda>_. map_of a name = None) False (eset (l_ffld e name) b a)"  
    unfolding l_ffld_def by (e_vcg simp: update_conv)


subsection \<open>Address Values\<close>
text \<open>
  An address holds a memory block, and a path into the value stored there, 
  which identifies the part of that value the pointer points to.
\<close>

datatype subscript = 
  is_Idx: Idx (the_Idx: nat) 
| is_Memb: Memb (the_Memb: mname)
interpretation Idx: l_C1 is_Idx the_Idx subscript.Idx "EDynamic EPtr"
  by unfold_locales simp_all
interpretation Memb: l_C1 is_Memb the_Memb subscript.Memb "EDynamic EPtr"
  by unfold_locales simp_all

hide_const (open) Idx Memb
type_synonym subpath = "subscript list"

type_synonym block_idx = nat

type_synonym addr = "block_idx \<times> subpath"

subsection \<open>Values\<close>

datatype val = 
  Null                                    -- \<open>Null pointer\<close>
| is_I: I (the_I: int_val)                -- \<open>Integer\<close>
| is_Addr: Addr (the_Addr: addr)          -- \<open>Non-null pointer\<close>  
| is_Array: Array (the_Array: "val list") -- \<open>Array (Block of consecutive values)\<close>
| is_Struct: Struct (the_Struct: "(mname \<times> val) list")  -- \<open>Struct (Name-value assignment)\<close>
| Uninit                                  -- \<open>Uninitialized value\<close>

interpretation I: l_C1 is_I the_I I "EStatic EType" by (unfold_locales) auto
interpretation Addr: l_C1 is_Addr the_Addr Addr "EStatic EType" by (unfold_locales) auto
interpretation Array: l_C1 is_Array the_Array Array "EStatic EType" by (unfold_locales) auto
interpretation Struct: l_C1 is_Struct the_Struct Struct "EStatic EType" by (unfold_locales) auto

(*definition l_Struct :: "(val,(mname\<times>val) list,_) elens" where 
  "l_Struct \<equiv> ( \<lambda>(Struct _ ms) \<Rightarrow> return ms | _ \<Rightarrow> EAssert type_error,
     \<lambda>ms. \<lambda>(Struct sn _) \<Rightarrow> return (Struct sn ms) | _ \<Rightarrow> EAssert type_error)"
 
lemma elens_Struct[simp]: "elens (l_Struct)"
  apply unfold_locales
  unfolding l_Struct_def
  by (auto split: val.splits)

lemma struct_get_spec[e_vcg]:
  "e_spec (\<lambda>ms. is_Struct v \<and> ms = the_Struct v) (\<lambda>e. \<not>is_Struct v \<and> e=type_error) False (eget l_Struct v)"
  apply (cases v)
  by (auto simp: l_Struct_def)

lemma struct_set_spec[e_vcg]:
  "e_spec (\<lambda>v'. \<exists>n ms'. v=Struct n ms' \<and> v'=Struct n ms) (\<lambda>e. \<not>is_Struct v \<and> e=type_error) False (eset l_Struct ms v)"
  apply (cases v)
  by (auto simp: l_Struct_def)

lemma [simp]: 
  "\<not>is_nonterm (eget l_Struct a)"
  "\<not>is_nonterm (eset l_Struct b a)"
  by (auto simp: l_Struct_def split: val.splits)
*)
hide_const (open) Null I Addr Array Struct Uninit

subsection \<open>Paths into Values\<close>
primrec l_subscript :: "subscript \<Rightarrow> (val,val,_) elens" where
  "l_subscript (subscript.Idx i) = Array.l o\<^sub>l l_nth (EDynamic EOverflow) i"
| "l_subscript (subscript.Memb name) = Struct.l o\<^sub>l l_ffld (EStatic EStructure) name"

lemma l_subscript_alt: "l_subscript ss = (case ss of
  (subscript.Idx i) \<Rightarrow> Array.l o\<^sub>l l_nth (EDynamic EOverflow) i
| (subscript.Memb name) \<Rightarrow> Struct.l o\<^sub>l l_ffld (EStatic EStructure) name)"
  by (auto split: subscript.splits)

primrec l_subpath :: "subpath \<Rightarrow> (val,val,_) elens" where
  "l_subpath [] = l_id"
| "l_subpath (s#ss) = l_subscript s o\<^sub>l l_subpath ss"

lemma elens_subscript[simp]: "elens (l_subscript ss)"
  by (cases ss) simp_all

lemma elens_subpath[simp]: "elens (l_subpath p)"
  by (induction p) auto

subsection \<open>Memory\<close>

datatype mem_block = is_Block: Block ty (the_Block: val) | is_Freed: Freed ty

primrec block_ty :: "mem_block \<Rightarrow> ty" where
  "block_ty (Block ty _) = ty" | "block_ty (Freed ty) = ty"

definition l_Block :: "(mem_block,val,_) elens" where
  "l_Block \<equiv> (
    \<lambda>(Block _ v) \<Rightarrow> return v | _ \<Rightarrow> EAssert pointer_error,
    \<lambda>v. \<lambda>(Block ty _) \<Rightarrow> return (Block ty v) | _ \<Rightarrow> EAssert pointer_error)"

lemma elens_Block[simp]: "elens (l_Block)"
  apply unfold_locales
  unfolding l_Block_def
  by (auto split: mem_block.splits)

lemma struct_get_spec[e_vcg]:
  "e_spec (\<lambda>ms. is_Block v \<and> ms = the_Block v) (\<lambda>e. \<not>is_Block v \<and> e=pointer_error) False (eget l_Block v)"
  apply (cases v)
  by (auto simp: l_Block_def)

lemma struct_set_spec[e_vcg]:
  "e_spec (\<lambda>v'. \<exists>n ms'. v=Block n ms' \<and> v'=Block n ms) (\<lambda>e. \<not>is_Block v \<and> e=pointer_error) False (eset l_Block ms v)"
  apply (cases v)
  by (auto simp: l_Block_def)

lemma [simp]: 
  "\<not>is_nonterm (eget l_Block a)"
  "\<not>is_nonterm (eset l_Block b a)"
  by (auto simp: l_Block_def split: mem_block.splits)


(*interpretation Block!: l_C1 is_Block the_Block Block "EDynamic EPtr"
  by (unfold_locales) auto
*)

type_synonym memory = "mem_block list"

definition is_valid_block :: "memory \<Rightarrow> nat \<Rightarrow> bool" where
  "is_valid_block m bi \<equiv> bi<length m \<and> \<not>is_Freed (m!bi)"

abbreviation assert_valid_block :: "memory \<Rightarrow> nat \<hookrightarrow> unit" where
  "assert_valid_block m bi \<equiv> assert (is_valid_block m bi) (EDynamic EPtr)"

text \<open>Memory can only hold positive sized values\<close>
fun nonzerosize_val :: "val \<Rightarrow> bool" where
  "nonzerosize_val val.Null \<longleftrightarrow> True"
| "nonzerosize_val (val.I _) \<longleftrightarrow> True"
| "nonzerosize_val (val.Addr _) \<longleftrightarrow> True"
| "nonzerosize_val (val.Array vs) \<longleftrightarrow> (\<exists>v\<in>set vs. nonzerosize_val v)"
| "nonzerosize_val (val.Struct ms) \<longleftrightarrow> (\<exists>(_,v)\<in>set ms. nonzerosize_val v)"
| "nonzerosize_val (val.Uninit) \<longleftrightarrow> True"

definition raw_alloc :: "ty \<Rightarrow> val \<Rightarrow> memory \<hookrightarrow> (block_idx \<times> memory)" where
  "raw_alloc ty v m \<equiv> do {
    assert (nonzerosize_val v) type_error;
    let idx = length m;
    let m = m@[Block ty v];
    return (idx,m)
  }"

definition raw_free :: "block_idx \<Rightarrow> memory \<hookrightarrow> memory"  where
  "raw_free bi m \<equiv> do {
    assert_valid_block m bi;
    let ty = block_ty (m!bi);
    let m = m[bi:=Freed ty];
    return m
  }"

definition l_raw_mem :: "block_idx \<Rightarrow> (memory,val,_) elens" where
  "l_raw_mem bi \<equiv> l_nth (EDynamic EPtr) bi o\<^sub>l l_Block"

lemma elens_raw_mem[simp]: "elens (l_raw_mem bi)"
  unfolding l_raw_mem_def by simp



subsection \<open>Types\<close>


fun new_val :: "ty \<Rightarrow> val" where
  "new_val ty.Null = val.Uninit"
| "new_val ty.I = val.Uninit"
| "new_val (ty.Ptr _) = val.Uninit"
| "new_val (ty.StructPtr _) = val.Uninit"
| "new_val (ty.Array sz ty) = val.Array (replicate sz (new_val ty))"
| "new_val (ty.Struct sn ms) = val.Struct (map (\<lambda>(x,T). (x, new_val T)) ms)"

definition alloc :: "ty \<Rightarrow> memory \<hookrightarrow> (addr\<times>memory)" 
where
  "alloc ty \<mu> \<equiv> do {
    (bi,\<mu>) \<leftarrow> raw_alloc ty (new_val ty) \<mu>;
    return ((bi,[]),\<mu>)
  }"


definition calloc :: "ty \<Rightarrow> nat \<Rightarrow> memory \<hookrightarrow> (addr\<times>memory)" 
  -- \<open>Allocate an array of memory objects. Array size must be greater 0,
      as a zero size results in undefined behaviour. \<close>
where
  "calloc ty n \<mu> \<equiv> do {
    assert (n>0) overflow_error; 
    let ty = ty.Array n ty;
    (bi,\<mu>) \<leftarrow> raw_alloc ty (new_val ty) \<mu>;
    return ((bi,[subscript.Idx 0]),\<mu>)
  }"

definition cp_alloc :: "ty \<Rightarrow> val \<Rightarrow> memory \<hookrightarrow> (addr\<times>memory)" where
  "cp_alloc ty v \<mu> \<equiv> do {
    (bi,\<mu>) \<leftarrow> raw_alloc ty v \<mu>;
    return ((bi,[]),\<mu>)
  }"

definition free :: "addr \<Rightarrow> memory \<hookrightarrow> memory" where
  "free \<equiv> \<lambda>(bi,p) \<mu>. do {
    (* Frees both, pointers created by cp_alloc and by calloc *)
    assert (p=[] \<or> p=[subscript.Idx 0]) pointer_error;
    raw_free bi \<mu>
  }"

definition l_addr :: "addr \<Rightarrow> (memory,val,_) elens" where
  "l_addr \<equiv> \<lambda>(bi,p). l_raw_mem bi o\<^sub>l l_subpath p"

lemma elens_addr[simp]: "elens (l_addr addr)" by (simp add: l_addr_def split: prod.split)

context 
  fixes SM :: struct_map
  fixes \<mu> :: memory
begin

definition MT :: "nat \<rightharpoonup> ty" where
  "MT i \<equiv> if i<length \<mu> then Some (block_ty (\<mu>!i)) else None"

definition FREE :: "nat set" where
  "FREE \<equiv> { i . i<length \<mu> \<and> is_Freed (\<mu>!i) }"

fun nty_eq :: "ty \<Rightarrow> ty \<Rightarrow> bool" where
  "nty_eq (ty.StructPtr sn1) (ty.StructPtr sn2) \<longleftrightarrow> sn1=sn2"
| "nty_eq (ty.StructPtr sn1) (ty.Ptr (ty.Struct sn2 _)) \<longleftrightarrow> sn1 = sn2"
| "nty_eq (ty.Ptr (ty.Struct sn1 _)) (ty.StructPtr sn2) \<longleftrightarrow> sn1 = sn2"
| "nty_eq (ty.Ptr (ty.Struct sn1 _)) (ty.Ptr (ty.Struct sn2 _)) \<longleftrightarrow> sn1 = sn2"
| "nty_eq ty1 ty2 \<longleftrightarrow> ty1=ty2"

lemma nty_eq_refl[simp]:
  "nty_eq ty ty"
  apply (cases "(ty,ty)" rule: nty_eq.cases)
  apply (auto)
  done

lemma nty_eq_sym: "nty_eq ty1 ty2 \<longleftrightarrow> nty_eq ty2 ty1"
  apply (cases "(ty1, ty2)" rule: nty_eq.cases)
  by auto

lemma nty_eq_trans[trans]: "\<lbrakk>nty_eq ty1 ty2; nty_eq ty2 ty3\<rbrakk> \<Longrightarrow> nty_eq ty1 ty3"
  apply (cases "(ty1, ty2)" rule: nty_eq.cases)
  apply simp_all
  apply (cases "(ty1, ty3)" rule: nty_eq.cases)
  apply simp_all
  apply (cases "(ty2, ty3)" rule: nty_eq.cases)
  apply simp_all
  apply (cases "(ty1, ty3)" rule: nty_eq.cases)
  apply simp_all
  done  


fun wt_path :: "ty \<Rightarrow> ty \<Rightarrow> subpath \<Rightarrow> bool" where
  "wt_path T ty [] \<longleftrightarrow> nty_eq ty T"
| "wt_path T (ty.Array _ ty) (subscript.Idx _ # ss) \<longleftrightarrow> wt_path T ty ss"
| "wt_path T (ty.Struct _ ms) (subscript.Memb name # ss) \<longleftrightarrow> (
    case map_of ms name of
      None \<Rightarrow> False
    | Some ty \<Rightarrow> wt_path T ty ss  
    )"
| "wt_path _ _ _ \<longleftrightarrow> False"

lemma nty_eq_nostruct_is_eq[simp]: 
  "\<lbrakk>\<not>ty.is_StructPtr ty; \<not>ty.is_Ptr ty\<rbrakk> \<Longrightarrow> nty_eq ty ty' \<longleftrightarrow> ty=ty'"
  apply (cases ty; cases ty')
  apply (auto split: Option.bind_splits)
  done

lemma nty_eq_ptr_cases:
  assumes "nty_eq (ty.Ptr ty1) ty2"
  obtains 
    ty2' where "ty2 = ty.Ptr ty2'" "ty1=ty2'"
  | sn ms1 where "ty1 = ty.Struct sn ms1" "ty2 = ty.StructPtr sn"  
  | sn ms1 ms2 where "ty1 = ty.Struct sn ms1" "ty2 = ty.Ptr (ty.Struct sn ms2)"
  using assms
  apply (cases "(ty.Ptr ty1,ty2)" rule: nty_eq.cases)
  apply auto
  done

lemma nty_eq_struct_ptr_cases:
  assumes "nty_eq (ty.StructPtr sn) ty2"
  obtains 
    "ty2 = ty.StructPtr sn"
  | ms2 where "ty2 = ty.Ptr (ty.Struct sn ms2)"  
  using assms
  apply (cases "(ty.StructPtr sn,ty2)" rule: nty_eq.cases)
  apply auto
  done


lemma wt_path_cong: "nty_eq ty ty' \<Longrightarrow> wt_path T ty p \<longleftrightarrow> wt_path T ty' p"
  apply (induction T ty p arbitrary: ty' rule: wt_path.induct)
  apply (auto split: )
  apply (metis nty_eq_trans nty_eq_sym)  
  apply (metis nty_eq_trans)  
  apply (auto elim!: nty_eq_ptr_cases) []
  apply (auto elim!: nty_eq_struct_ptr_cases) []
  apply (auto elim!: nty_eq_ptr_cases) []
  apply (auto elim!: nty_eq_struct_ptr_cases) []
  done

lemma wt_path_cong2: "nty_eq T T' \<Longrightarrow> wt_path T ty p \<longleftrightarrow> wt_path T' ty p"
  apply (induction T ty p arbitrary: T' rule: wt_path.induct)
  apply (auto split: option.splits)
  apply (metis nty_eq_trans)  
  apply (metis nty_eq_trans nty_eq_sym)  
  done

inductive wt_addr:: "ty \<Rightarrow> addr \<Rightarrow> bool" where
  "\<lbrakk> MT bi = Some bty; wt_path T bty p \<rbrakk> \<Longrightarrow> wt_addr T (bi,p)"

inductive wt_val:: "ty \<Rightarrow> val \<Rightarrow> bool" where
  "wt_val (ty.Null) (val.Null)"
| "wt_val (ty.I) (val.I _)"
| "wt_val (ty.Ptr ty) (val.Null)"
| "\<lbrakk> wt_addr ty addr \<rbrakk> \<Longrightarrow> wt_val (ty.Ptr ty) (val.Addr addr)"
| "wt_val (ty.StructPtr ty) (val.Null)"
| "\<lbrakk> SM sname = Some mts; wt_addr (ty.Struct sname mts) addr \<rbrakk> 
    \<Longrightarrow> wt_val (ty.StructPtr sname) (val.Addr addr)"
| "\<lbrakk> length vs = sz; \<forall>i < sz. wt_val ty (vs!i) \<rbrakk> \<Longrightarrow> wt_val (ty.Array sz ty) (val.Array vs)"
| "\<lbrakk> dom (map_of mts) = dom (map_of ms); 
      \<forall>n T v. map_of mts n = Some T \<and> map_of ms n = Some v \<longrightarrow> wt_val T v \<rbrakk> 
     \<Longrightarrow> wt_val (ty.Struct sname mts) (val.Struct ms)"
| "wt_val (ty.Null) (val.Uninit)"
| "wt_val (ty.I) (val.Uninit)"
| "wt_val (ty.Ptr _) (val.Uninit)"
| "wt_val (ty.StructPtr _) (val.Uninit)"

definition wt_block :: "mem_block \<Rightarrow> bool" where 
  "wt_block \<equiv> \<lambda>
    (Block ty v) \<Rightarrow> wt_val ty v \<and> wf_ty SM ty \<and> nonzero_ty ty \<and> nonzerosize_val v 
  | (Freed ty) \<Rightarrow> nonzero_ty ty \<and> wf_ty SM ty"

definition wt_mem :: "bool" where
  "wt_mem \<equiv> \<forall>blk\<in>set \<mu>. wt_block blk"

inductive_simps wt_val_ty_conv: 
  "wt_val (ty.I) v"
  "wt_val (ty.Ptr ty) v"
  "wt_val (ty.StructPtr sn) v"
  "wt_val (ty.Array n ty) v"
  "wt_val (ty.Struct sn mts) v"
  "wt_val (ty.Null) v"

end

lemma wt_mem_empty[simp]: "wt_mem SM []"
  by (auto simp: wt_mem_def)


lemma MT_wf_ty:
  assumes "wt_mem SM \<mu>"
  assumes "MT \<mu> bi = Some bty"
  shows "wf_ty SM bty"
  using assms
  apply (auto simp: MT_def wt_mem_def 
    split: split_if_asm)
  apply (auto dest!: nth_mem[of bi \<mu>] dest!: bspec)
  apply (auto simp: wt_block_def split: mem_block.splits)
  done


context wf_program_loc begin

lemma wt_path_append[simp]: 
  assumes "wf_ty SM ty"  
  shows "wt_path T ty (p1@p2) \<longleftrightarrow> 
    (\<exists>ty'. wf_ty SM ty' \<and> wt_path ty' ty p1 \<and> wt_path T ty' p2)"
  using assms  
  apply (induction T ty p1 rule: wt_path.induct)
  apply (auto split: option.splits)
  using wt_path_cong apply blast
  apply (auto simp: SM_mt_wf) []
  apply (auto simp: SM_mt_wf) [] 
  done

lemma wt_path_cons[simp]:
  assumes "NO_MATCH [] p2"
  assumes "wf_ty SM ty"  
  shows "wt_path T ty (s # p2) = (\<exists>ty'. wf_ty SM ty' \<and> wt_path ty' ty [s] \<and> wt_path T ty' p2)"
  using wt_path_append[of ty T "[s]" p2, OF assms(2)] by simp

  lemma wt_val_cong:
    assumes "nty_eq ty ty'"
    assumes "wf_ty SM ty" "wf_ty SM ty'"
    shows "wt_val SM \<mu> ty b \<longleftrightarrow> wt_val SM \<mu> ty' b"
    using assms
    apply (cases "(ty,ty')" rule: nty_eq.cases)
    apply simp_all
    apply (auto intro!: wt_val.intros elim!: wt_val.cases)
    done
  
  lemma wt_addr_cong:
    assumes "nty_eq ty ty'"
    assumes "wf_ty SM ty" "wf_ty SM ty'"
    shows "wt_addr \<mu> ty addr \<longleftrightarrow> wt_addr \<mu> ty' addr"
    using assms wt_path_cong2
    by (auto simp: wt_addr.simps)  

end

definition mem_ord :: "memory \<Rightarrow> memory \<Rightarrow> bool" (infix "\<subseteq>\<^sub>\<mu>" 50) where
  "\<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<equiv> length \<mu> \<le> length \<mu>' 
    \<and> (\<forall>i<length \<mu>. block_ty (\<mu>!i) = block_ty (\<mu>'!i))
    \<and> (\<forall>i<length \<mu>. is_Freed (\<mu>!i) \<longrightarrow> is_Freed (\<mu>'!i))"

lemma mem_ord_alt: "\<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<longleftrightarrow> MT \<mu> \<subseteq>\<^sub>m MT \<mu>' \<and> FREE \<mu> \<subseteq> FREE \<mu>'"
  apply rule
  apply (auto simp: mem_ord_def map_le_def MT_def dom_def FREE_def) []
  using leI apply (auto simp: mem_ord_def map_le_def MT_def dom_def FREE_def split: split_if_asm) []
  done

definition mem_eq :: "memory \<Rightarrow> memory \<Rightarrow> bool" (infix "=\<^sub>\<mu>" 50) where
  "\<mu> =\<^sub>\<mu> \<mu>' \<equiv> \<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<and> \<mu>' \<subseteq>\<^sub>\<mu> \<mu>"

lemma mem_ord_refl[simp]: "\<mu> \<subseteq>\<^sub>\<mu> \<mu>"
  by (auto simp: mem_ord_def)

lemma mem_ord_trans[trans]: "\<lbrakk>\<mu>1 \<subseteq>\<^sub>\<mu> \<mu>2; \<mu>2 \<subseteq>\<^sub>\<mu> \<mu>3\<rbrakk> \<Longrightarrow> \<mu>1 \<subseteq>\<^sub>\<mu> \<mu>3"
  by (auto simp: mem_ord_def)

lemma mem_ord_antisym: "\<lbrakk> \<mu> \<subseteq>\<^sub>\<mu> \<mu>'; \<mu>'\<subseteq>\<^sub>\<mu> \<mu> \<rbrakk> \<Longrightarrow> \<mu> =\<^sub>\<mu> \<mu>'"
  unfolding mem_eq_def by auto

lemma mem_eq_refl[simp]: "\<mu> =\<^sub>\<mu> \<mu>"
  unfolding mem_eq_def by auto

lemma mem_eq_sym: "\<mu> =\<^sub>\<mu> \<mu>' \<Longrightarrow> \<mu>' =\<^sub>\<mu> \<mu>"
  unfolding mem_eq_def by auto

lemma mem_eq_trans[trans]: "\<lbrakk>\<mu>1 =\<^sub>\<mu> \<mu>2; \<mu>2 =\<^sub>\<mu> \<mu>3\<rbrakk> \<Longrightarrow> \<mu>1 =\<^sub>\<mu> \<mu>3"
  by (auto simp: mem_eq_def dest: mem_ord_trans)

lemma mem_eq_alt: 
  "\<mu> =\<^sub>\<mu> \<mu>' \<longleftrightarrow> MT \<mu> = MT \<mu>' \<and> FREE \<mu> = FREE \<mu>'"
  unfolding mem_eq_def mem_ord_alt
  by (auto intro: map_le_antisym)

lemma mem_eqD1: "\<mu> =\<^sub>\<mu> \<mu>' \<Longrightarrow> \<mu> \<subseteq>\<^sub>\<mu> \<mu>'" by (auto simp: mem_eq_def)
lemma mem_eqD2: "\<mu> =\<^sub>\<mu> \<mu>' \<Longrightarrow> \<mu>' \<subseteq>\<^sub>\<mu> \<mu>" by (auto simp: mem_eq_def)


lemma wt_addr_mono:
  assumes "wt_addr \<mu> T addr"  
  assumes "mem_ord \<mu> \<mu>'"   
  shows "wt_addr \<mu>' T addr"  
  using assms
  by (auto elim!: wt_addr.cases intro: wt_addr.intros simp: mem_ord_alt)

lemma wt_val_mono:
  assumes "wt_val SM \<mu> T v"  
  assumes "\<mu> \<subseteq>\<^sub>\<mu> \<mu>'"   
  shows "wt_val SM \<mu>' T v"
  using assms(1,2)
  by induction (auto intro: wt_val.intros dest: wt_addr_mono)

lemma wt_new_val[simp]: "wt_val SM \<mu> T (new_val T)"
  apply (induction T)
  apply (auto intro: wt_val.intros)
  apply (rule wt_val.intros)
  apply (auto simp: map_of_map)
  apply rprems
  apply (erule map_of_SomeD)
  by (simp add: snds.simps) (* TODO: This should be in default simpset! *)


lemma nonzero_ty_imp_nonzerosize_val:
  assumes "wt_val SM \<mu> ty v"
  assumes "nonzero_ty ty"
  shows "nonzerosize_val v"
  using assms
  apply induction
  apply auto
  apply (auto simp: in_set_conv_nth Bex_def) []
  apply (rename_tac mts ms)  
  apply (case_tac mts; case_tac ms; simp)
  apply (auto)
  by (metis (full_types) case_prodI domD insert_iff map_of_SomeD snd_conv) 


 
lemma raw_alloc_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"  
  assumes "wt_val SM \<mu> ty v"  
  assumes "nonzero_ty ty" "wf_ty SM ty"
  shows "nd_spec (\<lambda>(bi,\<mu>'). 
    bi\<ge>length \<mu> \<and> MT \<mu>' bi = Some ty \<and> \<mu> \<subseteq>\<^sub>\<mu> \<mu>'
  \<and> wt_mem SM \<mu>') (raw_alloc ty v \<mu>)"
proof -
  have MTSS: "\<mu> \<subseteq>\<^sub>\<mu> (\<mu> @ [Block ty v])"
    by (auto simp: mem_ord_def nth_append)

  show ?thesis  
    using assms MTSS
    unfolding raw_alloc_def Let_def
    by (fastforce 
      simp: wt_mem_def nth_append MT_def wt_block_def 
      simp: nonzero_ty_imp_nonzerosize_val
      split: mem_block.splits intro: wt_val_mono[OF _ MTSS])
qed    


lemma alloc_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"  
  assumes "nonzero_ty ty" "wf_ty SM ty"
  shows "nd_spec (\<lambda>(addr,\<mu>'). 
    \<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<and> wt_mem SM \<mu>' \<and> wt_addr \<mu>' ty addr) (alloc ty \<mu>)"
proof -
  show ?thesis  
    using assms
    unfolding alloc_def 
    apply (e_vcg 
      intro!: wt_new_val 
      simp: wt_addr.simps wt_val_ty_conv
      split: prod.splits)
    done
qed    


lemma calloc_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"  
  assumes "nonzero_ty ty" "wf_ty SM ty"
  shows "nd_spec (\<lambda>(addr,\<mu>'). 
    \<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<and> wt_mem SM \<mu>' \<and> wt_addr \<mu>' ty addr) (calloc ty n \<mu>)"
proof -
  show ?thesis  
    using assms
    unfolding calloc_def 
    apply (e_vcg 
      intro!: wt_new_val 
      simp: wt_addr.simps wt_val_ty_conv
      split: prod.splits)
    done
qed    

lemma cp_alloc_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"  
  assumes "wt_val SM \<mu> ty v"  
  assumes "nonzero_ty ty" "wf_ty SM ty"
  shows "nd_spec (\<lambda>(addr,\<mu>'). 
    \<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<and> wt_mem SM \<mu>' \<and> wt_addr \<mu>' ty addr) (cp_alloc ty v \<mu>)"
proof -
  show ?thesis  
    using assms
    unfolding cp_alloc_def 
    apply (e_vcg intro!: wt_new_val simp: wt_addr.simps split: prod.splits)
    done
qed    

    
lemma raw_free_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"  
  shows "nd_spec (\<lambda>\<mu>'. \<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<and> wt_mem SM \<mu>') (raw_free bi \<mu>)"
proof -
  have "nd_spec (\<lambda>\<mu>'. \<mu> \<subseteq>\<^sub>\<mu> \<mu>') (raw_free bi \<mu>)"
    unfolding raw_free_def 
    by (e_vcg simp: is_valid_block_def mem_ord_def nth_list_update)
  hence aux: "\<And>P. nd_spec (\<lambda>\<mu>'. \<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<longrightarrow> P \<mu>') (raw_free bi \<mu>) \<Longrightarrow> nd_spec P (raw_free bi \<mu>)"
    by (simp add: pw_espec_iff)

  show ?thesis  
    apply (rule aux)
    using assms
    unfolding raw_free_def 
    apply e_vcg
    unfolding wt_mem_def
    apply clarify

    apply (auto simp: wt_block_def split: mem_block.splits)
    using set_update_subset_insert wt_val_mono apply fastforce
    apply (metis insertE mem_block.distinct(2) set_update_subset_insert subsetCE)
    apply (metis insertE mem_block.distinct(2) set_update_subset_insert subsetCE)
    apply (metis insertE mem_block.distinct(2) set_update_subset_insert subsetCE)
    apply (metis block_ty.simps(1) insertE is_valid_block_def mem_block.collapse(1) mem_block.exhaust_disc mem_block.sel(3) nth_mem set_update_subset_insert subsetCE)
    apply (metis block_ty.simps(1) insertE is_valid_block_def mem_block.collapse(1) mem_block.exhaust_disc mem_block.sel(3) nth_mem set_update_subset_insert subsetCE)
    done
qed    

lemma free_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  shows "nd_spec (\<lambda>\<mu>'. \<mu> \<subseteq>\<^sub>\<mu> \<mu>' \<and> wt_mem SM \<mu>') (free addr \<mu>)"
  using assms unfolding free_def by (cases addr) e_vcg

lemma is_BlockE: assumes "is_Block b" obtains ty v where "b = Block ty v"
  using assms by (cases b) auto

lemma raw_mem_get_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  assumes "MT \<mu> bi = Some T"
  shows "nd_spec (wt_val SM \<mu> T) (eget (l_raw_mem bi) \<mu>)"
  using assms
  unfolding l_raw_mem_def wt_mem_def
  apply (e_vcg') 
  apply (auto elim!: is_BlockE simp: dom_def wt_block_def split: mem_block.splits)
  using MT_def nth_mem by fastforce


lemma raw_mem_set_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  assumes "MT \<mu> bi = Some T"
  assumes "wt_val SM \<mu> T v"
  shows "nd_spec (\<lambda>\<mu>'. wt_mem SM \<mu>' \<and> \<mu> =\<^sub>\<mu> \<mu>') (eset (l_raw_mem bi) v \<mu>)"
proof (cases "is_Freed (\<mu>!bi)")
  case True
  thus ?thesis
    by (e_vcg simp: l_raw_mem_def)

next
  case False
  with assms(2) obtain vh where X1: "\<mu>!bi = Block T vh" "bi<length \<mu>"
    by (cases "\<mu>!bi") (auto simp: MT_def split: split_if_asm)
  hence X2: "Block T vh \<in> set \<mu>"  
    by (auto simp: in_set_conv_nth)

  have MTSS: "\<mu> \<subseteq>\<^sub>\<mu> \<mu>[bi := Block T v]"
    using assms(2) X1
    by (auto simp: mem_ord_def MT_def nth_list_update split: split_if_asm)

  from assms(1) have [simp]: "nonzero_ty T" "wf_ty SM T" 
    unfolding wt_mem_def MT_def wt_block_def
    using X2 by auto

  with assms(3) have [simp]: "nonzerosize_val v" 
    by (blast intro: nonzero_ty_imp_nonzerosize_val)

  show ?thesis
    using assms  
    unfolding l_raw_mem_def wt_mem_def[abs_def]
    apply (e_vcg simp: in_set_conv_nth nth_list_update split: split_if_asm)
    apply (auto 
      simp: wt_block_def MT_def in_set_conv_nth nth_list_update Ball_def
      split: mem_block.splits split_if_asm 
      intro!: wt_val_mono[OF _ MTSS]) []
    apply fastforce
    apply fastforce
    apply (auto simp: mem_eq_alt MT_def[abs_def] nth_list_update FREE_def intro!: ext)
    done    
qed

context wf_program_loc
begin

context begin

private lemma dom_eq_SomeE: 
  assumes "dom a = dom b"  
  assumes "a k = Some x" 
  obtains y where "dom a = dom b" "b k = Some y"
  using assms by auto

lemma get_subpath_spec[e_vcg]:
  assumes "wt_path T bty p" 
  assumes "wt_val SM \<mu> bty b"
  assumes "wf_ty SM T" "wf_ty SM bty"
  shows "nd_spec (wt_val SM \<mu> T) (eget (l_subpath p) b)"
  using assms
  apply (induction bty p arbitrary: b rule: wt_path.induct)
  apply (simp_all)

  apply (e_vcg dest: wt_val_cong)

  apply (erule wt_val.cases; clarsimp)
  apply e_vcg

  apply (erule wt_val.cases; clarsimp split: option.splits)
  apply (erule (1) dom_eq_SomeE)
  apply (e_vcg simp: SM_mt_wf)
  done

lemma set_subpath_spec[e_vcg]:
  assumes "wt_path T bty p" 
  assumes "wt_val SM \<mu> bty b"
  assumes "wt_val SM \<mu> T v"
  assumes "wf_ty SM T" "wf_ty SM bty"
  shows "nd_spec (wt_val SM \<mu> bty) (eset (l_subpath p) v b)"
  using assms
  apply (induction bty p arbitrary: b rule: wt_path.induct)
  apply (simp_all)
  
  apply (e_vcg dest: wt_val_cong)

  apply (erule wt_val.cases; clarsimp)
  apply (e_vcg intro!: wt_val.intros simp: nth_list_update)

  apply (erule wt_val.cases; clarsimp split: option.splits)
  apply (erule (1) dom_eq_SomeE)
  apply (e_vcg simp: SM_mt_wf
      intro!: wt_val.intros elim: dom_eq_SomeE split: split_if_asm)
  done

end

lemma get_addr_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  assumes "wt_addr \<mu> T addr"
  assumes "wf_ty SM T"
  shows "nd_spec (wt_val SM \<mu> T) (eget (l_addr addr) \<mu>)"
  using assms(1,2,3)
  unfolding l_addr_def 
  apply (cases addr; clarsimp)
  apply (erule wt_addr.cases; clarsimp)
  apply (e_vcg simp: MT_wf_ty)
  done

lemma set_addr_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  assumes "wt_addr \<mu> T addr"
  assumes "wt_val SM \<mu> T v"
  assumes "wf_ty SM T"
  shows "nd_spec (\<lambda>\<mu>'. wt_mem SM \<mu>' \<and> \<mu> =\<^sub>\<mu> \<mu>') (eset (l_addr addr) v \<mu>)"
  using assms
  unfolding l_addr_def 
  apply (cases addr; clarsimp)
  apply (erule wt_addr.cases; clarsimp)
  apply (e_vcg simp: MT_wf_ty)
  done
end

subsection \<open>Memory Related Operations\<close>

definition is_allocated_raw :: "memory \<Rightarrow> nat \<Rightarrow> bool" where
  "is_allocated_raw \<mu> bi \<equiv> bi<length \<mu> \<and> is_Block (\<mu>!bi)"

definition is_allocated :: "memory \<Rightarrow> addr \<Rightarrow> bool" where
  "is_allocated \<mu> \<equiv> \<lambda>(bi,_). is_allocated_raw \<mu> bi"

definition resolve_subpath_array :: "val \<Rightarrow> subpath \<hookrightarrow> subpath \<times> nat \<times> nat" 
  -- \<open>Get index and array size for sub-path to array element.
    Throws pointer-error if this is not a path to an array. \<close>
where
  "resolve_subpath_array v p \<equiv> do {
    j \<leftarrow> eget (l_last pointer_error o\<^sub>l Idx.l) p;
    p' \<leftarrow> eget (l_butlast pointer_error) p;
    vs \<leftarrow> eget (l_subpath p' o\<^sub>l Array.l) v;
    return (p',j,length vs)
  }"


definition index_subpath :: "val \<Rightarrow> int \<Rightarrow> subpath \<hookrightarrow> subpath" where
  "index_subpath v i p \<equiv> do {
    (_,j,len) \<leftarrow> resolve_subpath_array v p;
    let j = int j + i;
    assert (j \<ge> 0 \<and> nat j\<le>len) (EDynamic EPtr);
    p \<leftarrow> eset (l_last (EDynamic EPtr) o\<^sub>l Idx.l) (nat j) p;
    return p
  }"

definition index_addr :: "memory \<Rightarrow> int \<Rightarrow> addr \<hookrightarrow> addr" where
  "index_addr \<equiv> \<lambda>\<mu> i (bi,p). do {
    v \<leftarrow> eget (l_raw_mem bi) \<mu>;
    p \<leftarrow> index_subpath v i p;
    return (bi,p)
  }"

definition cnv_array_to_eptr :: "memory \<Rightarrow> addr \<hookrightarrow> addr" 
  -- \<open>Convert address of array to address of its first element\<close>
where
  "cnv_array_to_eptr \<mu> \<equiv> \<lambda>(bi,p). do {
    eget (l_addr (bi,p) o\<^sub>l Array.l) \<mu>;
    return (bi,p@[subscript.Idx 0])
  }"



lemma norm_wt_subscript: "NO_MATCH 0 n \<Longrightarrow> 
  wt_path T ty [subscript.Idx n] \<longleftrightarrow> wt_path T ty [subscript.Idx 0]"
  by (cases ty) auto

context wf_program_loc begin

lemma index_subpath_spec[e_vcg]:
  assumes "wt_val SM \<mu> ty v"
  assumes "wt_path T ty p"  
  assumes "wf_ty SM T" "wf_ty SM ty"
  shows "nd_spec (wt_path T ty) (index_subpath v i p)"
  using assms
  unfolding index_subpath_def resolve_subpath_array_def
  apply (cases p rule: rev_cases)
  apply e_vcg
  apply (e_vcg elim!: Idx.E Array.E elim: wt_val.cases simp: norm_wt_subscript)
  done

lemma index_addr_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  assumes "wt_addr \<mu> T addr"
  assumes "wf_ty SM T"
  shows "nd_spec (wt_addr \<mu> T) (index_addr \<mu> i addr)"
  using assms
  unfolding index_addr_def
  apply -
  apply (erule wt_addr.cases)
  apply (e_vcg intro: wt_addr.intros MT_wf_ty)
  done

lemma cnv_array_to_eptr_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  assumes "wt_addr \<mu> (ty.Array n T) addr"
  assumes "wf_ty SM (ty.Array n T)"
  shows "nd_spec (wt_addr \<mu> T) (cnv_array_to_eptr \<mu> addr)"
  using assms
  unfolding cnv_array_to_eptr_def
  apply -
  apply (erule wt_addr.cases)
  apply (e_vcg 
    intro!: wt_addr.intros exI[where x="ty.Array n T"] 
    simp: MT_wf_ty wt_val_ty_conv)
  done
  

end

definition diff_subpath :: "val \<Rightarrow> subpath \<Rightarrow> subpath \<hookrightarrow> int" where
  "diff_subpath v p1 p2 \<equiv> do {
    (p1',i1,l) \<leftarrow> resolve_subpath_array v p1;
    (p2',i2,_) \<leftarrow> resolve_subpath_array v p2;
    assert (p1'=p2') (EDynamic EPtr);
    return (int i1 - int i2)
  }"

definition diff_addr :: "memory \<Rightarrow> addr \<Rightarrow> addr \<hookrightarrow> int" where
  "diff_addr \<equiv> \<lambda>\<mu> (bi1,p1) (bi2,p2). do {
    assert (is_allocated_raw \<mu> bi1) pointer_error;
    assert (is_allocated_raw \<mu> bi2) pointer_error;
    assert (bi1 = bi2) (EDynamic EPtr);
    v \<leftarrow> eget (l_raw_mem bi2) \<mu>;
    diff_subpath v p1 p2
  }"


context wf_program_loc begin
lemma diff_subpath_spec[e_vcg]:
  assumes "wt_val SM \<mu> ty v"
  assumes "wt_path T ty p1"  
  assumes "wt_path T ty p2"  
  assumes "wf_ty SM ty"
  shows "nd_spec (\<lambda>_. True) (diff_subpath v p1 p2)"
  using assms
  unfolding diff_subpath_def resolve_subpath_array_def
  apply (e_vcg elim!: Idx.E Array.E elim: wt_val.cases simp: norm_wt_subscript)
  done

lemma diff_addr_spec[e_vcg]:
  assumes "wt_mem SM \<mu>"
  assumes "wt_addr \<mu> T addr1"
  assumes "wt_addr \<mu> T addr2"
  assumes "wf_ty SM T"
  shows "nd_spec (\<lambda>_. True) (diff_addr \<mu> addr1 addr2)"
  using assms
  unfolding diff_addr_def
  apply (cases addr1, cases addr2)
  apply (e_vcg elim!: wt_addr.cases intro: MT_wf_ty)
  done
end

definition memb_subpath :: "val \<Rightarrow> mname \<Rightarrow> subpath \<hookrightarrow> subpath" where
  "memb_subpath v name p \<equiv> do {
    let p = p@[subscript.Memb name];
    eget (l_subpath p) v;
    return p
  }"

definition memb_addr :: "memory \<Rightarrow> mname \<Rightarrow> addr \<hookrightarrow> addr" where
  "memb_addr \<equiv> \<lambda>\<mu> name (bi,p). do {
    v \<leftarrow> eget (l_raw_mem bi) \<mu>;
    p \<leftarrow> memb_subpath v name p;
    return (bi,p)
  }"

context wf_program_loc begin

lemma memb_subpath_spec[e_vcg]:
  assumes "wt_val SM \<mu> ty v"
  assumes "wt_path (ty.Struct sname ms) ty p"  
  assumes "map_of ms name = Some T"
  assumes "wf_ty SM ty" "wf_ty SM (ty.Struct sname ms)"
  shows "nd_spec (wt_path T ty) (memb_subpath v name p)"
  using assms
  unfolding memb_subpath_def
  apply (clarsimp simp: Let_def)
  apply (rule e_vcg)
  apply clarsimp
  apply (rule e_cons, rule e_vcg)
  apply (subst wt_path_append)
  apply (assumption)
  defer
  apply assumption
  apply (erule (1) SM_mt_wf)
  apply (auto intro!: exI[where x="(ty.Struct sname ms)"])
  done

lemma memb_addr_spec[e_vcg]: 
  assumes "wt_mem SM \<mu>"
  assumes "wt_addr \<mu> (ty.Struct sname ms) addr"
  assumes "map_of ms name = Some T"
  assumes "wf_ty SM (ty.Struct sname ms)"
  shows "nd_spec (wt_addr \<mu> T) (memb_addr \<mu> name addr)"  
  using assms
  unfolding memb_addr_def
  by (e_vcg elim!: wt_addr.cases intro: wt_addr.intros MT_wf_ty)

end

fun valid_subpath :: "val \<Rightarrow> subpath \<Rightarrow> bool" where
  "valid_subpath v [] \<longleftrightarrow> True"
| "valid_subpath (val.Array vs) ([subscript.Idx i]) \<longleftrightarrow> i\<le>length vs"
| "valid_subpath (val.Array vs) (subscript.Idx i#p) \<longleftrightarrow> i<length vs \<and> valid_subpath (vs!i) p"
| "valid_subpath (val.Struct ms) (subscript.Memb n#p) \<longleftrightarrow> 
    (case map_of ms n of None \<Rightarrow> False | Some v \<Rightarrow> valid_subpath v p)"
| "valid_subpath _ _ \<longleftrightarrow> False"

definition valid_addr :: "memory \<Rightarrow> addr \<Rightarrow> bool" where
  "valid_addr \<mu> \<equiv> \<lambda>(bi,p). bi<length \<mu> \<and> (
    case \<mu>!bi of
      Freed ty \<Rightarrow> False
    | Block ty v \<Rightarrow> valid_subpath v p  
  )"

fun readable_subpath :: "val \<Rightarrow> subpath \<Rightarrow> bool" where
  "readable_subpath v [] \<longleftrightarrow> True"
| "readable_subpath (val.Array vs) (subscript.Idx i#p) \<longleftrightarrow> i<length vs \<and> readable_subpath (vs!i) p"
| "readable_subpath (val.Struct ms) (subscript.Memb n#p) \<longleftrightarrow> 
    (case map_of ms n of None \<Rightarrow> False | Some v \<Rightarrow> readable_subpath v p)"
| "readable_subpath _ _ \<longleftrightarrow> False"

definition readable_addr :: "memory \<Rightarrow> addr \<Rightarrow> bool" where
  "readable_addr \<mu> \<equiv> \<lambda>(bi,p). bi<length \<mu> \<and> (
    case \<mu>!bi of
      Freed ty \<Rightarrow> False
    | Block ty v \<Rightarrow> readable_subpath v p  
  )"


context wf_program_loc begin

lemma l_subpath_iff_readable_spec: "e_spec 
  (\<lambda>_. readable_subpath v p) 
  (\<lambda>_. \<not>readable_subpath v p) 
  False 
  (eget (l_subpath p) v)"
proof -
  note [e_vcg del] = get_subpath_spec

  show ?thesis
    apply (induction v p rule: readable_subpath.induct)
    (* TODO: Why does splitting in e_vcg not work ?*)
    apply (e_vcg simp: l_subscript_alt;auto split: subscript.splits; e_vcg)+
    done
qed

lemma l_addr_iff_readable_spec: "e_spec 
  (\<lambda>_. readable_addr \<mu> addr) 
  (\<lambda>_. \<not>readable_addr \<mu> addr) 
  False 
  (eget (l_addr addr) \<mu>)"
proof -
  note [e_vcg del] = get_subpath_spec

  show ?thesis
    apply (cases addr)
    apply (clarsimp simp: readable_addr_def l_addr_def l_raw_mem_def)
    apply (e_vcg' vcg: l_subpath_iff_readable_spec)
    apply (auto split: mem_block.splits)    
    done
qed


lemma "readable_subpath v p \<Longrightarrow> valid_subpath v p"
  apply (induction v p rule: valid_subpath.induct)
  apply (auto split: option.splits)
  done

lemma readable_addr_alt: 
  "readable_addr \<mu> addr \<longleftrightarrow> (\<exists>v. eget (l_addr addr) \<mu> = return v)"
  using l_addr_iff_readable_spec[of \<mu> addr] 
  apply (cases "eget (l_addr addr) \<mu>")
  apply (auto simp: pw_espec_iff)
  done

end  

datatype ptr_comp_res = PC_EQ | PC_NEQ | PC_LESS | PC_GREATER


definition compare_addr :: "memory \<Rightarrow> addr \<Rightarrow> addr \<hookrightarrow> ptr_comp_res" where
  "compare_addr \<mu> addr1 addr2 \<equiv> do {
    assert (valid_addr \<mu> addr1) pointer_error;
    assert (valid_addr \<mu> addr2) pointer_error;

    let (bi1,p1) = addr1;
    let (bi2,p2) = addr2;

    if bi1\<noteq>bi2 then do {
      (* Force addresses to be in allocated range, otherwise
        the result is undefined due to overlap effects *)
      assert (readable_addr \<mu> addr1) pointer_error;
      assert (readable_addr \<mu> addr2) pointer_error;
      return PC_NEQ
    } else do {
      let (prf,r1,r2) = split_common_prefix p1 p2;
  
      case (r1,r2) of
        ([],[]) \<Rightarrow> return PC_EQ
      | ([],_) \<Rightarrow> EAssert pointer_error  
      | (_,[]) \<Rightarrow> EAssert pointer_error  
      | (s1#rr1, s2#rr2) \<Rightarrow> do {
          (* Do not compare address with its prefix: They might be equal
            due to zero-indexing --- however, we set it to undefined. *)
          assert (rr1=[] \<longleftrightarrow> rr2=[]) pointer_error;
          (* If the path continues, force addresses to be in range, otherwise
            the result is undefined due to overlap effects *)
          assert (rr1\<noteq>[] \<longrightarrow> readable_addr \<mu> addr1 \<and> readable_addr \<mu> addr2) pointer_error;
          case (s1,s2) of
            (subscript.Idx i1, subscript.Idx i2) \<Rightarrow> 
              if i1<i2 then return PC_LESS else return PC_GREATER
          | (subscript.Memb _, subscript.Memb _) \<Rightarrow> return PC_NEQ
          | _ \<Rightarrow> EAssert pointer_error (* TODO: Might want type-error here?! *)
        }
    }
  }"

definition "addr_less \<mu> addr1 addr2 \<equiv> do {
  pc \<leftarrow> compare_addr \<mu> addr1 addr2;
  case pc of
    PC_EQ \<Rightarrow> return False
  | PC_NEQ \<Rightarrow> EAssert pointer_error
  | PC_LESS \<Rightarrow> return True
  | PC_GREATER \<Rightarrow> return False 
}"

definition "addr_leq \<mu> addr1 addr2 \<equiv> do {
  pc \<leftarrow> compare_addr \<mu> addr1 addr2;
  case pc of
    PC_EQ \<Rightarrow> return True
  | PC_NEQ \<Rightarrow> EAssert pointer_error
  | PC_LESS \<Rightarrow> return True
  | PC_GREATER \<Rightarrow> return False 
}"

definition "addr_eq \<mu> addr1 addr2 \<equiv> do {
  pc \<leftarrow> compare_addr \<mu> addr1 addr2;
  case pc of
    PC_EQ \<Rightarrow> return True
  | PC_NEQ \<Rightarrow> return False
  | PC_LESS \<Rightarrow> return False
  | PC_GREATER \<Rightarrow> return False 
}"

lemma is_allocated_rawE:
  assumes "is_allocated_raw \<mu> bi"
  obtains ty v where "bi<length \<mu>" "\<mu>!bi = Block ty v"
  using assms
  apply (cases "\<mu>!bi")
  apply (auto simp: is_allocated_raw_def)
  done

lemma wt_mem_block_imp:
  assumes "\<mu>!bi = Block ty v"
  assumes "bi < length \<mu>"
  assumes "wt_mem SM \<mu>" 
  shows 
    "MT \<mu> bi = Some ty" 
    "wt_val SM \<mu> ty v" "wf_ty SM ty" "nonzero_ty ty" "nonzerosize_val v"
  using assms
  unfolding wt_mem_def wt_block_def
  by (auto simp: Ball_def in_set_conv_nth MT_def)  

lemma wt_path_idx_conv: "wt_path T ty (subscript.Idx i#p) 
  \<longleftrightarrow> (\<exists>n mty. ty=ty.Array n mty \<and> wt_path T mty p)"
  apply (cases "(T,ty,subscript.Idx i#p)" rule: wt_path.cases)
  apply auto
  done

context wf_program_loc begin

lemma compare_addr_spec[e_vcg]:
  (*assumes "wt_mem SM \<mu>" 
  assumes "wt_addr \<mu> T addr1"
  assumes "wt_addr \<mu> T addr2"
  assumes "wf_ty SM T"*)
  shows "nd_spec (\<lambda>_. True) (compare_addr \<mu> addr1 addr2)"
  (*using assms(1-3)*)
  unfolding compare_addr_def
  apply (e_vcg')
  apply (clarsimp split: prod.split list.split subscript.split; safe?; clarsimp)
  apply e_vcg
  apply e_vcg
  apply e_vcg
  apply e_vcg
  apply e_vcg
  done

end
end
