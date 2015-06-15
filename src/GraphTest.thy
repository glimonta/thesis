theory GraphTest
imports "Network_Security_Policy_Verification/Lib/FiniteListGraph" SmallStep Pretty
begin

text \<open>This will be the content for the nodes, V is for values, U is for
  uninitialized and P is for pointer to another node.\<close>
datatype node_content = Val int_val | U | P nat | InvalidP

record node =
  id :: nat
  content :: node_content

definition g :: "node list_graph" where
  "g \<equiv> \<lparr> nodesL = [], edgesL = [] \<rparr>"

type_synonym id_mem = "(nat \<times> val option) list option list"
type_synonym block_mem = "val option list"
type_synonym id_block_mem = "(nat \<times> val option) list"

(* n is the last id number used the nodes *)
fun add_id_to_block :: "nat \<Rightarrow> block_mem \<Rightarrow> (nat \<times> id_block_mem)" where
  "add_id_to_block n [] = (n, [])"
| "add_id_to_block n (x#xs) = 
    (let (n', m) = add_id_to_block (n+1) xs
    in (n', (n+1, x) # m))"

fun add_id_to_mem :: "nat \<Rightarrow> mem \<Rightarrow> id_mem" where
  "add_id_to_mem n [] = []"
| "add_id_to_mem n (x#xs) = (case x of
    None \<Rightarrow> None # add_id_to_mem n xs |
    Some block \<Rightarrow>
      let (n', bl) = add_id_to_block n block
      in Some bl # add_id_to_mem n' xs
  )"

fun enumerate_mem :: "mem \<Rightarrow> id_mem" where
  "enumerate_mem m = add_id_to_mem 0 m"

value "enumerate_mem [Some [Some (I 1), Some (I 2), Some (I 3)], None, Some [Some (I 4), Some (I 5), Some (A (0,1))]]"

abbreviation "mem \<equiv> [Some [Some (I 1), Some (I 2), Some (I 3)], None, Some [Some (I 4), Some (I 5), Some (A (0,1))]]"

value "create_nodes (enumerate_mem mem) (enumerate_mem mem)"

fun valid_id_mem :: "addr \<Rightarrow> id_mem \<Rightarrow> bool" where
  "valid_id_mem (i,j) \<mu> = (
    if i<length \<mu> then (
      case \<mu>!i of
        None \<Rightarrow> False
      | Some b \<Rightarrow> 0\<le>j \<and> nat j < length b)
    else False)"

fun create_node :: "id_mem \<Rightarrow> nat \<times> val option \<Rightarrow> node" where
  "create_node m (n, None) = \<lparr>id = n, content = U\<rparr>"
| "create_node m (n, (Some v)) = (case v of
      NullVal \<Rightarrow> \<lparr>id = n, content = InvalidP\<rparr> |
      I iv \<Rightarrow> \<lparr>id = n, content = (Val iv)\<rparr> |
      A (i,j) \<Rightarrow> (case (valid_id_mem (i,j) m) of
        True \<Rightarrow> let id = fst (the (m!i) !! j)
          in \<lparr>id = n, content = (P id)\<rparr> |
        False \<Rightarrow> \<lparr>id = n, content = InvalidP\<rparr>)
    )"

fun create_block_edges :: "id_mem \<Rightarrow> id_block_mem \<Rightarrow> node list_graph" where
  "create_block_edges m [] = \<lparr> nodesL = [], edgesL = [] \<rparr>"
| "create_block_edges m (_#[]) = \<lparr> nodesL = [], edgesL = [] \<rparr>"
| "create_block_edges m (x#y#xs) =
      (let
        node1 = create_node m x;
        node2 = create_node m y
      in 
        add_edge node1 node2 (create_block_edges m (y#xs)))"

fun create_edges :: "id_mem \<Rightarrow> id_mem \<Rightarrow> node list_graph" where
  "create_edges m [] = \<lparr> nodesL = [], edgesL = [] \<rparr>"
| "create_edges m (x#xs) = (case x of
    None \<Rightarrow> create_edges m xs |
    Some ys \<Rightarrow>
      (let
        g = create_block_edges m ys;
        ng = (nodesL g);
        eg = (edgesL g);
        g' = create_edges m xs;
        ng' = (nodesL g');
        eg' = (edgesL g')
      in
        \<lparr> nodesL = remdups (ng @ ng'), edgesL = remdups (eg @ eg') \<rparr>
      )
  )"

value "create_edges (enumerate_mem mem) (enumerate_mem mem)"

fun lookup_node :: "nat \<Rightarrow> node list \<Rightarrow> node option" where
  "lookup_node _ [] = None"
| "lookup_node n (x#xs) = (if (id x) = n then Some x else lookup_node n xs)"

fun create_pointer_edges :: "node list \<Rightarrow> node list_graph \<Rightarrow> node list_graph" where
  "create_pointer_edges [] ng = ng"
| "create_pointer_edges (x#xs) ng = (case (content x) of
    (P n) \<Rightarrow> (case (lookup_node n (nodesL ng)) of
      Some node \<Rightarrow> add_edge x node (create_pointer_edges xs ng) |
      None \<Rightarrow> create_pointer_edges xs ng) |
    _ \<Rightarrow> create_pointer_edges xs ng
  )"

abbreviation "testgraph \<equiv> create_edges (enumerate_mem mem) (enumerate_mem mem)"

value "create_pointer_edges (nodesL testgraph) testgraph"

fun construct_graph :: "mem \<Rightarrow> node list_graph" where
  "construct_graph xs = 
    (let
      id_mem = enumerate_mem xs;
      graph = (create_edges id_mem id_mem)
    in
      create_pointer_edges (nodesL graph) graph
    )"

value "construct_graph mem"

value "construct_graph [None, Some [(Some (I 43)), Some (I (-56))], Some [(Some (A (0,0))), Some (I 4), None]]"

fun shows_node_content :: "node_content \<Rightarrow> shows" where
  "shows_node_content (Val i) = shows_prec 0 i"
| "shows_node_content (U) = shows ''?''"
| "shows_node_content (P n) = shows ''*'' o shows n"
| "shows_node_content (InvalidP) = shows ''<invalid>''"

fun shows_node :: "node \<Rightarrow> shows" where
  "shows_node x = shows_paren (shows (id x) o shows '', '' o shows_node_content (content x))"

fun shows_edge :: "node \<times> node \<Rightarrow> shows" where
  "shows_edge (x,y) = shows_paren (shows_sep shows_node (shows '', '') [x,y])"

value "shows_node \<lparr>node.id = 1, content = Val 43\<rparr> ''''"

fun shows_graph :: "node list_graph \<Rightarrow> shows" where
  "shows_graph graph =
    shows ''['' o
    (shows_sep shows_node (shows '', '') (nodesL graph)) o
    shows '']'' o
    shows_nl o
    shows ''['' o
    (shows_sep shows_edge (shows '', '') (edgesL graph)) o
    shows '']''"

value "shows_graph (construct_graph [None, Some [(Some (I 43)), Some (I (-56))], Some [(Some (A (0,0))), Some (I 4), None]]) ''''"

end