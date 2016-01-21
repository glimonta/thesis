section \<open>Stack\<close>
theory Stack
imports Memory Eval
begin

  text \<open>In this theory, we model the stack and the stack operations required
    for entering and leaving functions.\<close>

  text \<open>A stack frame has a current CFG-node, a valuation of the local variables,
    and an address where the return value should be copied to.\<close>
  type_synonym stack_frame = "fun_decl \<times> com \<times> valuation \<times> addr option"

  type_synonym stack = "stack_frame list"


  definition create_frame :: "fun_decl \<Rightarrow> val list \<Rightarrow> addr option \<Rightarrow> memory \<hookrightarrow> (stack_frame \<times> memory)" 
  where
    "create_frame fd args rv \<mu> \<equiv> do {
      (av,\<mu>) \<leftarrow> alloc_params (fun_decl.params fd) args \<mu>;
      (lv,\<mu>) \<leftarrow> alloc_vdecls (fun_decl.locals fd) \<mu>;
      let lv = av ++ lv;
      return ((fd,fun_decl.body fd, lv, rv), \<mu>)
    }"

  definition destroy_frame :: "stack_frame \<Rightarrow> memory \<hookrightarrow> memory" where
    "destroy_frame \<equiv> \<lambda>(fd,_,lv,_) \<mu>. do {
      let names = map fst (fun_decl.params fd @ fun_decl.locals fd);
      efold (\<lambda>x \<mu>. do {
        let addr = the (lv x);
        free addr \<mu>
      }) names \<mu>
    }"

  type_synonym state = "stack \<times> valuation \<times> memory"  

  definition comp_evs :: "stack \<Rightarrow> valuation \<Rightarrow> valuation" where 
    "comp_evs \<equiv> \<lambda>((_,_,l,_)#_) \<Rightarrow> (\<lambda>\<gamma>. \<gamma>++l)"

  term eval_exp  

  definition op_call 
    :: "addr option \<Rightarrow> fun_decl \<Rightarrow> val list \<Rightarrow> state \<hookrightarrow> state" 
    where
    "op_call rv fd args \<equiv> \<lambda>(stk,\<gamma>,\<mu>). do {
      (fr,\<mu>) \<leftarrow> create_frame fd args rv \<mu>;
      return (fr#stk,\<gamma>,\<mu>)
    }"

  definition assign_return_value :: "addr option \<Rightarrow> res option \<Rightarrow> memory \<hookrightarrow> memory" where
    "assign_return_value rl v \<mu> \<equiv> do {
      v \<leftarrow> 
        case v of 
          None \<Rightarrow> return None 
        | Some v \<Rightarrow> do {v \<leftarrow> to_rval \<mu> v; return (Some v)};

      case (rl,v) of
        (None,_) \<Rightarrow> return \<mu>
      | (Some addr, Some v) \<Rightarrow> eset (l_addr addr) v \<mu>
      | _ \<Rightarrow> EAssert type_error
    }"

  definition op_return  
    :: "res option \<Rightarrow> state \<hookrightarrow> state"
    where
    "op_return v \<equiv> \<lambda>(stk,\<gamma>,\<mu>). do {
      assert (stk\<noteq>[]) type_error;
      let fr = hd stk;
      let (_,_,_,rl) = fr;
      \<mu> \<leftarrow> assign_return_value rl v \<mu>;
      \<mu> \<leftarrow> destroy_frame fr \<mu>;
      return (tl stk,\<gamma>,\<mu>)
    }"
  



end
