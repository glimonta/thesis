theory Check_Execute
imports SmallStep "../Typing/Type_Checker"
begin

  definition initial_state :: "program \<hookrightarrow> state" where
    "initial_state p \<equiv> do {
      let \<mu> = [];
      (\<gamma>,\<mu>) \<leftarrow> alloc_vdecls (program.globals p) \<mu>;
      fd \<leftarrow> lookup_fun p main_fname;
      (fr,\<mu>) \<leftarrow> create_frame fd [] None \<mu>;
      return ([fr],\<gamma>,\<mu>)
    }"
  
  (* TODO: Move *)  
  definition map_error :: "('e \<Rightarrow> 'f) \<Rightarrow> ('a,'e) error \<Rightarrow> ('a,'f) error" where
    "map_error f m \<equiv> case m of 
      return x \<Rightarrow> return x 
    | EAssert e \<Rightarrow> EAssert (f e) 
    | ENonterm \<Rightarrow> ENonterm"


  type_synonym 'a cke = "('a,ck_error + chloe_error) error"  

  definition check_execute :: "program \<Rightarrow> state cke" where
    "check_execute p \<equiv> do {
      map_error Inl (wt_program p);
      s \<leftarrow> map_error Inr (initial_state p);
      map_error Inr (interp p s)
    }"



  partial_function (error) interpn :: "nat \<Rightarrow> _" where "
    interpn n p s = (
      if n=0 \<or> is_term (return s) then
        return s
      else do {
        s \<leftarrow> ss_step p s;
        interpn (n - 1) p s
      }
    )"

  declare interpn.simps[code]  

  definition execn :: "nat \<Rightarrow> program \<hookrightarrow> state" where
    "execn n p \<equiv> do {
      s \<leftarrow> initial_state p;
      interpn n p s
    }"



end
