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

  text \<open>A valuation can be initialized from a variable declaration list,
    by allocating a new block of memory for each variable.\<close>
  definition alloc_vdecls :: "vdecl list \<Rightarrow> memory \<hookrightarrow> (valuation\<times>memory)" where
    "alloc_vdecls l \<mu> \<equiv> efold (\<lambda>(vname,ty) (vals,\<mu>). do {
      (addr,\<mu>) \<leftarrow> alloc ty \<mu>;
      let vals = vals(vname \<mapsto> addr);
      return (vals,\<mu>)
      }) l (Map.empty,\<mu>)"
  
  text \<open>A valuation can also be initialized from a parameter declaration list and a value list\<close>      
  definition alloc_params :: "vdecl list \<Rightarrow> val list \<Rightarrow> memory \<hookrightarrow> (valuation\<times>memory)" where
    "alloc_params vdecls vs \<mu> \<equiv> do {
      assert (length vdecls = length vs) structural_error;
      efold (\<lambda>((name,ty),v) (vals,\<mu>). do {
        (addr,\<mu>) \<leftarrow> cp_alloc ty v \<mu>;
        let vals = vals(name \<mapsto> addr);
        return (vals,\<mu>)
      }) (zip vdecls vs) (Map.empty,\<mu>)
    }"

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

  (* TODO/FIXME/BUG: We should protect memory allocated by stack-frames from being freed explicitely! 
    In particular for globals, this is important: Currently, our semantics allows
      "free &x" where x is a global!

    While we can argue that this will yield an error late for locals, i.e., on returning 
    from the function, it still seems somewhat scary to allow such a behaviour.

    Ideas for solution:
      1) Allocate frame with an T[1] - indirection, such that you never obtain a block pointer
          by referencing locals, globals, or parameters.

      2) Flag blocks as being statically allocated. Check for that on explicit free instruction.

      #2 seems somewhat cleaner by explicitly addressing the problem, while #1 is a hack 
        indirectly exploiting that only block-base pointers can be freed, assuming that one
        can never obtain the base-pointer from a deeper pointer.

    *)  

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
