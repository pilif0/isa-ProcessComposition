theory ProcessPort
  imports
    ProcessComposition.ProcessPaths
    PortGraph.PortGraph
begin

section\<open>Process Ports\<close>

text\<open>
  With process paths providing a unique identifier for subprocesses, we can use ports to uniquely
  identify individual occurrences of resources in parallel parts of process inputs/outputs within
  a larger composition.
  This is useful, for instance, when visualising processes to identify connection points.

  To implement this, the sides, labels and name atoms of general ports need to be specified.
  For labels of process ports we use resources and for names we use process paths.
  For port sides we introduce a new type with two elements, input and output, and prove it to be an
  instance of the @{class side_in_out} type class.
\<close>

subsection\<open>Resource Labels\<close>

text\<open>Turn parallel parts of a resource into ports (on some side and starting at some index)\<close>
fun parallelPorts :: "nat \<Rightarrow> 's \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('s, ('a, 'b) resource) port list"
  where "parallelPorts n s a = listPorts n s (parallel_parts a)"

lemma parallelPorts_length [simp]:
  "length (parallelPorts n s r) = length (parallel_parts r)"
  by simp

lemma distinct_parallelPorts [simp]:
  "distinct (parallelPorts n s r)"
  by (simp del: listPorts.simps)

lemma parallelPorts_par:
  " parallelPorts n s (a \<odot> b)
  = parallelPorts n s a @ parallelPorts (n + length (parallel_parts a)) s b"
  by (simp add: add.assoc zip_append2 parallel_parts_par)

lemma portSetSide_parallelPorts [simp]:
  "map (portSetSide s) (parallelPorts n s' x) = parallelPorts n s x"
  by clarsimp

subsection\<open>Process Side\<close>

text\<open>Process ports use just two sides: input and output\<close>
datatype process_side = In | Out
hide_const (open) process_side.In process_side.Out

text\<open>This satisfies the class we define when introducing ports\<close>
instantiation process_side :: side_in_out
begin

definition "In = process_side.In"
definition "Out = process_side.Out"

instance
  by standard (simp add: In_process_side_def Out_process_side_def)
end

text\<open>We use the simplifier to prefer the syntax introduced by the class\<close>
lemmas [simp] = In_process_side_def[symmetric] Out_process_side_def[symmetric]

text\<open>This set of sides is finite\<close>
lemma UNIV_process_side [simp]:
  "UNIV = {In, Out :: process_side}"
  unfolding In_process_side_def Out_process_side_def
  by (metis UNIV_eq_I insertI1 insertI2 process_side.exhaust)

instance process_side :: finite
  by standard simp

text\<open>Any process side not being either input or output is a contradiction\<close>
lemma process_side_neither [simp]:
    fixes x :: process_side
  assumes "x \<noteq> In"
      and "x \<noteq> Out"
    shows False
  using assms by (cases x) simp_all

subsection\<open>Checking Validity\<close>

text\<open>
  Port is valid for a process if there is a corresponding resource in the parallel parts of its
  input/output
\<close>
definition port_valid ::
    "(process_side, ('a, 'b) resource) port \<Rightarrow> ('a, 'b, 'l, 'm) process \<Rightarrow> bool"
  where "port_valid p x =
  ( let r = (case port.side p of process_side.In \<Rightarrow> input | process_side.Out \<Rightarrow> output) x in
    let rs = parallel_parts r in
    port.index p < length rs \<and> rs ! (port.index p) = port.label p)"

text\<open>Qualified port is valid if the name is a path to a subtree where the port is valid\<close>
definition qualified_port_valid ::
    " (process_side, ('a, 'b) resource, process_inner) qualified_port \<Rightarrow>
      ('a, 'b, 'l, 'm) process \<Rightarrow> bool"
  where "qualified_port_valid qp x =
  ( case subprocess (qualified_port.name qp) x of
      Some x \<Rightarrow> port_valid (qualified_port.port qp) x
    | None \<Rightarrow> False)"

text\<open>Any input port generated from the input of a process is valid\<close>
lemma
  notes [simp del] = In_process_side_def[symmetric]
  shows "port \<in> set (parallelPorts 0 In (input x)) \<Longrightarrow> port_valid port x"
  by (cases x ; clarsimp simp add: in_set_zip port_valid_def Let_def In_process_side_def)

text\<open>Any output port generated from the output of a process is valid\<close>
lemma
  notes [simp del] = Out_process_side_def[symmetric]
  shows "port \<in> set (parallelPorts 0 Out (output x)) \<Longrightarrow> port_valid port x"
  by (cases x ; clarsimp simp add: port_valid_def Let_def in_set_zip Out_process_side_def)

end