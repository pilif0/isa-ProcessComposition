theory ProcessCatSubtype
  imports
    ProcessComposition_PortGraph.ProcessPortGraph
begin

section\<open>Processes With Port Graphs\<close>

text\<open>
  We will be using port graphs in relating process compositions that should be seen as equal by the
  eventual category.
  For this we need a subtype of process compositions containing only those that have a defined port
  graph construction, expressed by the @{const pgDefined} predicate.
\<close>

text\<open>Define the subtype and set up lifting for it\<close>
typedef ('a, 'b, 'l, 'm) proc = "{p :: ('a, 'b, 'l, 'm) process . pgDefined p}"
proof
  show "Identity Empty \<in> {p. pgDefined p}"
    by simp
qed
setup_lifting type_definition_proc

text\<open>Lift relevant resource actions\<close>
lift_definition
  Primitive :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Primitive by simp
lift_definition
  Identity :: "('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Identity by simp
lift_definition
  Swap :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Swap by simp
lift_definition
  Duplicate :: "'b \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Duplicate by simp
lift_definition
  Erase :: "'b \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Erase by simp
lift_definition
  Repeat :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Repeat by simp
lift_definition
  Once :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Once by simp
lift_definition
  Close :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Close by simp
lift_definition
  Forget :: "('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Forget by simp

text\<open>Lift relevant composition operations\<close>
lift_definition
  Seq :: "('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Seq by simp
lift_definition
  Par :: "('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b, 'l, 'm) proc"
  is Process.Par by simp

text\<open>Lift relevant operations on process compositions\<close>
lift_definition
  valid :: "('a, 'b, 'l, 'm) proc \<Rightarrow> bool"
  is Process.valid .
lift_definition
  input :: "('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b) resource"
  is Process.input .
lift_definition
  "output" :: "('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b) resource"
  is Process.output .

lift_definition
  map_process :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> ('a, 'c, 'e, 'g) proc \<Rightarrow> ('b, 'd, 'f, 'h) proc"
  is Process.map_process by simp

text\<open>Lift the port graph construction\<close>
lift_definition
  pgConstruct :: "('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b, 'l, 'm) process_port_graph"
  is ProcessPortGraph.pgConstruct .

text\<open>Lift the BNF structure\<close>
lift_bnf ('a, 'b, 'l, 'm) proc [wits: "Process.Identity Empty :: ('a, 'b, 'l, 'm) process"]
  by auto

end