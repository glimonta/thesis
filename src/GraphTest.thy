theory GraphTest
imports "Network_Security_Policy_Verification/Lib/FiniteListGraph" SmallStep Pretty
begin

text \<open>This will be the content for the nodes, V is for values, U is for
  uninitialized and P is for pointer to another node.\<close>
datatype node_content = Val int_val | U | P addr | InvalidP

record node =
  id :: addr
  content :: node_content

definition g :: "node list_graph" where
  "g \<equiv> \<lparr> nodesL = [], edgesL = [] \<rparr>"

type_synonym block_mem = "val option list"

abbreviation "mem \<equiv> [Some [Some (I 1), Some (I 2), Some (I 3)], None, Some [Some (I 4), Some (I 5), Some (A (0,1))]]"


fun create_node :: "mem \<Rightarrow> addr \<Rightarrow> val option \<Rightarrow> node" where
  "create_node m addr None = \<lparr>id = addr, content = U\<rparr>"
| "create_node m addr (Some v) = (case v of
      NullVal \<Rightarrow> \<lparr>id = addr, content = InvalidP\<rparr> |
      I iv \<Rightarrow> \<lparr>id = addr, content = (Val iv)\<rparr> |
      A (i,j) \<Rightarrow> (case (valid_mem (i,j) m) of
        True \<Rightarrow> \<lparr>id = addr, content = (P (i,j))\<rparr> |
        False \<Rightarrow> \<lparr>id = addr, content = InvalidP\<rparr>)
    )"

fun create_block_edges :: "mem \<Rightarrow> addr \<Rightarrow> block_mem \<Rightarrow> node list_graph" where
  "create_block_edges m (i,j) [] = \<lparr> nodesL = [], edgesL = [] \<rparr>"
| "create_block_edges m (i,j) (_#[]) = \<lparr> nodesL = [], edgesL = [] \<rparr>"
| "create_block_edges m (i,j) (x#y#xs) =
      (let
        node1 = create_node m (i, j) x;
        node2 = create_node m (i, j+1) y
      in 
        add_edge node1 node2 (create_block_edges m (i, j+1) (y#xs)))"

fun create_edges :: "mem \<Rightarrow> nat \<Rightarrow> mem \<Rightarrow> node list_graph" where
  "create_edges m n [] = \<lparr> nodesL = [], edgesL = [] \<rparr>"
| "create_edges m n (x#xs) = (case x of
    None \<Rightarrow> create_edges m (n+1) xs |
    Some ys \<Rightarrow>
      (let
        g = create_block_edges m (n,0) ys;
        ng = (nodesL g);
        eg = (edgesL g);
        g' = create_edges m (n+1) xs;
        ng' = (nodesL g');
        eg' = (edgesL g')
      in
        \<lparr> nodesL = remdups (ng @ ng'), edgesL = remdups (eg @ eg') \<rparr>
      )
  )"

value "create_edges mem 0 mem"

fun lookup_node :: "addr \<Rightarrow> node list \<Rightarrow> node option" where
  "lookup_node _ [] = None"
| "lookup_node addr (x#xs) = (if (id x) = addr then Some x else lookup_node addr xs)"

fun create_pointer_edges :: "node list \<Rightarrow> node list_graph \<Rightarrow> node list_graph" where
  "create_pointer_edges [] ng = ng"
| "create_pointer_edges (x#xs) ng = (case (content x) of
    (P n) \<Rightarrow> (case (lookup_node n (nodesL ng)) of
      Some node \<Rightarrow> add_edge x node (create_pointer_edges xs ng) |
      None \<Rightarrow> create_pointer_edges xs ng) |
    _ \<Rightarrow> create_pointer_edges xs ng
  )"

abbreviation "testgraph \<equiv> create_edges mem 0 mem"

value "create_pointer_edges (nodesL testgraph) testgraph"

fun construct_graph :: "mem \<Rightarrow> node list_graph" where
  "construct_graph xs = 
    (let
      graph = (create_edges mem 0 mem)
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
  "shows_node x = shows_paren (shows (A (id x)) o shows '', '' o shows_node_content (content x))"

fun shows_edge :: "node \<times> node \<Rightarrow> shows" where
  "shows_edge (x,y) = shows_paren (shows_sep shows_node (shows '', '') [x,y])"

value "shows_node \<lparr>node.id = (1, 0), content = Val 43\<rparr> ''''"

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