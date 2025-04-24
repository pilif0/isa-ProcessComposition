theory ProcessPortGraph
  imports
    ProcessComposition.ProcessPaths
    ProcessPort
    PortGraph.JuxSeqCommute
    PortGraph.NodePortGraph
    PortGraph.IdentityPortGraph
    PortGraph.SwapPortGraph
    PortGraph.ForkPortGraph
    PortGraph.EndPortGraph
    PortGraph.Equivalences
    PortGraph.PortGraphTrans
begin

section\<open>Process Port Graphs\<close>

text\<open>
  Port graphs constructed from process compositions underlie how process diagrams are drawn and are
  a step towards expressing the behaviour of process compositions.
  They turn the focus from how the process is built to how individual actions are interconnected.

  Currently we disregard optional composition and higher-order representation of compositions (and
  their related resource actions) because these require a more complex graphical model (at least
  hierarchical port graphs).
\<close>

text\<open>
  Nodes, which represent primitive actions, are annotated with a combination of that action's label
  and metadata
\<close>
datatype ('l, 'm) node_content =
    NodePrimitive 'l 'm

text\<open>
  Meaning process port graphs are port graphs with:
  \<^item> @{type process_side} as port sides,
  \<^item> resources as port labels,
  \<^item> @{type process_inner} as node name atoms, and
  \<^item> combination of label and metadata as node labels.
\<close>
type_synonym ('a, 'b, 'l, 'm) process_port_graph =
  "(process_side, ('a, 'b) resource, process_inner, ('l, 'm) node_content) port_graph"

subsection\<open>Basic Port Graphs\<close>

text\<open>
  On top of already introduced port graph patterns, we introduce some that are specific to process
  compositions
\<close>

subsubsection\<open>Forget\<close>

text\<open>Forget port graph has no node, it only connects a number of input ports to one output port\<close>
fun forgetPortGraph :: "('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) process_port_graph"
  where "forgetPortGraph x =
  PGraph
    []
    (map (\<lambda>p. Edge (OpenPort p) (OpenPort (Port Out 0 Anything))) (parallelPorts 0 In x))
    (parallelPorts 0 In x @ [Port Out 0 Anything])"

text\<open>Forget port graph is well-formed with flow\<close>
lemma port_graph_flow_forgetPortGraph:
  "port_graph_flow (forgetPortGraph x)" (is "port_graph_flow ?G")
proof unfold_locales
  fix e
  assume e: "e \<in> set (pg_edges ?G)"

  show "edge_from e \<in> set (pgraphPlaces ?G)"
    using e
    apply (clarsimp elim!: in_set_zipE del: disjCI simp add: split_beta set_zip image_Collect)
    apply (metis add_0 nth_upt)
    done

  show "edge_to e \<in> set (pgraphPlaces ?G)"
    using e by fastforce
next
  fix m n
  assume "m \<in> set (pg_nodes ?G)"
     and "n \<in> set (pg_nodes ?G)"
     and "node_name m = node_name n"
  then show "m = n"
    by simp
next
  fix p
  assume "p \<in> set (pg_ports ?G)"
  then show "port.index p < length (filter (\<lambda>x. port.side x = (port.side p)) (pg_ports ?G))"
    by (fastforce elim: in_set_zipE simp add: case_prod_beta)
next
  fix p q
  assume "p \<in> set (pg_ports ?G)"
    and "q \<in> set (pg_ports ?G)"
    and "port.side p = port.side q"
    and "port.index p = port.index q"
  then show "port.label p = port.label q"
    by (fastforce simp add: set_zip)
next
  fix n p q
  assume "n \<in> set (pg_nodes ?G)"
     and "p \<in> set (node_ports n)"
     and "q \<in> set (node_ports n)"
     and "port.side p = port.side q"
     and "port.index p = port.index q"
  then show "port.label p = port.label q"
    by simp
next
  show "distinct (pg_nodes ?G)"
    by simp
  show "distinct (pg_edges ?G)"
    by (simp add: distinct_map comp_def inj_on_def del: listPorts.simps)
  show "distinct (pg_ports ?G)"
    by (simp del: listPorts.simps) fastforce
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_open (edge_from e)"
  then show "place_side (edge_from e) = In"
    by (fastforce elim: in_set_zipE)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_open (edge_to e)"
  then show "place_side (edge_to e) = Out"
    by (fastforce elim: in_set_zipE)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_ground (edge_from e)"
  then show "place_side (edge_from e) = Out"
    by (fastforce elim: in_set_zipE)
next
  fix e
  assume "e \<in> set (pg_edges ?G)"
     and "place_ground (edge_to e)"
  then show "place_side (edge_to e) = In"
    by (fastforce elim: in_set_zipE)
qed

text\<open>Forget port graph is invariant under qualification\<close>
lemma qualifyPortGraph_forgetPortGraph [simp]:
  "qualifyPortGraph x (forgetPortGraph a) = forgetPortGraph a"
  by (fastforce elim: in_set_zipE simp add: qualifyPortGraph_def)

subsubsection\<open>Once\<close>

text\<open>
  Once port graph has no nodes, it only connects an input port directly to an output port.
  It is not identity because the edge's origin is labelled differently to its destination.
\<close>
(* TODO This could be generalised as a "wire" port graph, which would also generalise the identity port graph *)
fun oncePortGraph :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) process_port_graph"
  where "oncePortGraph a b =
  PGraph
    []
    [Edge (OpenPort (Port In 0 (Repeatable a b)))
          (OpenPort (Port Out 0 (Executable a b)))]
    [Port In 0 (Repeatable a b), Port Out 0 (Executable a b)]"

lemma port_graph_flow_oncePortGraph:
  "port_graph_flow (oncePortGraph a b)" (is "port_graph_flow ?G")
  by (unfold_locales ; fastforce)

text\<open>Once port graph is invariant under qualification\<close>
lemma qualifyPortGraph_oncePortGraph [simp]:
  "qualifyPortGraph x (oncePortGraph a b) = oncePortGraph a b"
  by (fastforce elim: in_set_zipE simp add: qualifyPortGraph_def)

subsection\<open>Port Graphs from Process Compositions\<close>

text\<open>
  The port graph construction is defined for process compositions without non-deterministic or
  higher-order features.
  That is, ones without:
  \<^item> Optional composition,
  \<^item> Injection actions for non-deterministic resources,
  \<^item> Distribution actions for non-deterministic resources,
  \<^item> Process representation as an executable resource, and
  \<^item> Application action for an executable resource.
\<close>
primrec pgDefined :: "('a, 'b, 'l, 'm) process \<Rightarrow> bool"
  where
    "pgDefined (Primitive ins outs l m) = True"
  | "pgDefined (Identity a) = True"
  | "pgDefined (Swap a b) = True"
  | "pgDefined (Seq p q) = (pgDefined p \<and> pgDefined q)"
  | "pgDefined (Par p q) = (pgDefined p \<and> pgDefined q)"
  | "pgDefined (Opt p q) = False"
  | "pgDefined (InjectL a b) = False"
  | "pgDefined (InjectR a b) = False"
  | "pgDefined (OptDistrIn a b c) = False"
  | "pgDefined (OptDistrOut a b c) = False"
  | "pgDefined (Duplicate a) = True"
  | "pgDefined (Erase a) = True"
  | "pgDefined (Represent p) = False"
  | "pgDefined (Apply a b) = False"
  | "pgDefined (Repeat a b) = True"
  | "pgDefined (Close a b) = True"
  | "pgDefined (Once a b) = True"
  | "pgDefined (Forget a) = True"

lemma pgDefined_map_process [simp]:
  "pgDefined (map_process f g h i x) = pgDefined x"
  by (induct x) simp_all

primrec pgConstruct :: "('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l, 'm) process_port_graph"
  where
    "pgConstruct (Primitive ins outs l m) =
      nodePortGraph [] (NodePrimitive l m) (parallel_parts ins) (parallel_parts outs)"
  | "pgConstruct (Seq p q) =
      seqPortGraphs (qualifyPortGraph SeqL (pgConstruct p)) (qualifyPortGraph SeqR (pgConstruct q))"
  | "pgConstruct (Par p q) =
      juxtapose (qualifyPortGraph ParL (pgConstruct p)) (qualifyPortGraph ParR (pgConstruct q))"
  | "pgConstruct (Identity a) = idPortGraph (parallel_parts a)"
  | "pgConstruct (Swap a b) = swapPortGraph (parallel_parts a) (parallel_parts b)"
  | "pgConstruct (Duplicate a) = forkPortGraph (Copyable a)"
  | "pgConstruct (Erase a) = endPortGraph [Copyable a]"
  | "pgConstruct (Repeat a b) = forkPortGraph (Repeatable a b)"
  | "pgConstruct (Close a b) = endPortGraph [Repeatable a b]"
  | "pgConstruct (Once a b) = oncePortGraph a b"
  | "pgConstruct (Forget a) = forgetPortGraph a"

text\<open>Results of the construction are well-formed port graphs with flow\<close>
lemma port_graph_flow_pgConstruct:
  assumes "pgDefined x"
    shows "port_graph_flow (pgConstruct x)"
  using assms
proof (induct x)
  case (Primitive x1 x2a x3 x4)
  then show ?case using port_graph_flow_nodePortGraph by simp
next
  case (Identity x)
  then show ?case using port_graph_flow_idPortGraph by simp
next
  case (Seq x1 x2)
  then show ?case
    using port_graph_flow_qualifyPortGraph port_graph_flow_seqPortGraphs qualifyPortGraph_apart
    by (metis pgConstruct.simps(2) pgDefined.simps(4) process_inner.distinct(1))
next
  case (Swap x1 x2a)
  then show ?case using port_graph_flow_swapPortGraph by simp
next
  case (Par x1 x2)
  then show ?case
    using port_graph_flow_qualifyPortGraph port_graph_flow_juxtapose qualifyPortGraph_apart
    by (metis pgConstruct.simps(3) pgDefined.simps(5) process_inner.distinct(23))
next case (Opt x1 x2) then show ?case by simp
next case (InjectL x1 x2a) then show ?case by simp
next case (InjectR x1 x2a) then show ?case by simp
next
  case (OptDistrIn x1 x2a x3)
  then show ?case by simp
next
  case (OptDistrOut x1 x2a x3)
  then show ?case by simp
next
  case (Duplicate x)
  then show ?case using port_graph_flow_forkPortGraph by simp
next
  case (Erase x)
  then show ?case using port_graph_flow_endPortGraph by (simp del: endPortGraph.simps)
next case (Represent x) then show ?case by simp
next case (Apply x1 x2a) then show ?case by simp
next case (Repeat x1 x2a) then show ?case using port_graph_flow_forkPortGraph by simp
next
  case (Close x1 x2a)
  then show ?case using port_graph_flow_endPortGraph by (simp del: endPortGraph.simps)
next case (Once x1 x2a) then show ?case using port_graph_flow_oncePortGraph by simp
next case (Forget x) then show ?case using port_graph_flow_forgetPortGraph by simp
qed

text\<open>Port graphs generated from process compositions contain no self loops\<close>
lemma pgConstruct_no_selfloop:
  assumes "pgDefined x"
      and "e \<in> set (pg_edges (pgConstruct x))"
    shows "edge_from e \<noteq> edge_to e"
proof -
  have "edge_in_flow e"
    using UNIV_process_side by (metis UNIV_I edge_in_flow_def)
  then show ?thesis
    using assms port_graph_flow_pgConstruct port_graph_flow.no_self_loop by blast
qed

text\<open>Open ports of the construction's result correspond to the composition's input and output\<close>
lemma pgConstruct_ports:
  assumes "pgDefined x"
    shows " set (pg_ports (pgConstruct x))
          = set ( listPorts 0 In (parallel_parts (input x))
                @ listPorts 0 Out (parallel_parts (output x)))"
  using assms
proof (induct x)
  case (Primitive x1 x2a x3 x4)
  then show ?case by simp
next
  case (Identity x)
  then show ?case by simp
next
  case (Seq x1 x2)
  then have " set (pg_ports (pgConstruct x1))
            = set (parallelPorts 0 In (input x1) @ parallelPorts 0 Out (output x1))"
        and " set (pg_ports (pgConstruct x2))
            = set (parallelPorts 0 In (input x2) @ parallelPorts 0 Out (output x2))"
    by simp_all
  then show ?case
    apply (cases "pgConstruct x1", cases "pgConstruct x2")
    apply (simp del: listPorts.simps)
    apply (subst (1 2) conj_disj_distribR)
    apply (subst (1 2) Collect_disj_eq)
    apply (subst (2 3) Collect_empty_eq[THEN iffD2])
    apply clarsimp
     apply clarsimp
    apply (simp only: Un_empty_left Un_empty_right)
    apply safe
    using process_side_neither apply metis
    using process_side_neither apply metis
    apply auto[1]
    by fastforce
next
  case (Swap x1 x2a)
  then show ?case by (simp add: parallel_parts_par)
next
  case (Par x1 x2)
  then have " set (pg_ports (pgConstruct x1))
            = set (parallelPorts 0 In (input x1) @ parallelPorts 0 Out (output x1))"
        and " set (pg_ports (pgConstruct x2))
            = set (parallelPorts 0 In (input x2) @ parallelPorts 0 Out (output x2))"
    by simp_all
  then show ?case
    apply (cases "pgConstruct x1", cases "pgConstruct x2")
    apply (simp del: listPorts.simps add: parallel_parts_par listPorts_append image_Un Un_assoc[symmetric])
    apply (subst (1 2) set_map[symmetric])
    apply (subst (1 2) shiftPort_listPorts)
    apply (subst (1 2) distinct_length_filter)
     apply (metis Par.prems(1) pgDefined.simps(5) port_graph.ports_distinct port_graph.sel(3) port_graph_flow_def port_graph_flow_pgConstruct)
    apply (simp del: listPorts.simps add: Int_Un_distrib)
    apply (subst (1 2) card_Un_disjnt)
    apply blast
         apply blast
        apply (simp del: listPorts.simps add: disjnt_def)
        apply safe[1]
    apply clarsimp
    apply blast
         apply blast
        apply (simp del: listPorts.simps add: disjnt_def)
        apply safe[1]
    apply clarsimp
    apply (subst (1 2 3 4) distinct_length_filter[symmetric], metis distinct_listPorts, metis distinct_listPorts)
    apply (simp del: listPorts.simps)
    apply blast
    done
next
  case (Opt x1 x2)
  then show ?case by simp
next
  case (InjectL x1 x2a)
  then show ?case by simp
next
  case (InjectR x1 x2a)
  then show ?case by simp
next
  case (OptDistrIn x1 x2a x3)
  then show ?case by simp
next
  case (OptDistrOut x1 x2a x3)
  then show ?case by simp
next
  case (Duplicate x)
  then show ?case by (simp add: parallel_parts_simps resource_par_def)
next
  case (Erase x)
  then show ?case by (simp add: parallel_parts_simps)
next
  case (Represent x)
  then show ?case by simp
next
  case (Apply x1 x2a)
  then show ?case by simp
next
  case (Repeat x1 x2a)
  then show ?case by (simp add: parallel_parts_simps resource_par_def)
next
  case (Close x1 x2a)
  then show ?case by (simp add: parallel_parts_simps)
next
  case (Once x1 x2a)
  then show ?case by (simp add: parallel_parts_simps)
next
  case (Forget x)
  then show ?case by (simp add: parallel_parts_simps)
qed

text\<open>Number of input ports matches number of input resource parallel parts\<close>
lemma pgConstruct_in_ports:
  assumes "pgDefined x"
    shows " length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x)))
          = length (parallel_parts (input x))"
  using assms
  apply (subst distinct_length_filter)
  using port_graph.ports_distinct port_graph_flow_def port_graph_flow_pgConstruct apply blast
  apply (subst pgConstruct_ports, assumption)
  apply (simp del: listPorts.simps add: Int_Un_distrib)
    apply (subst (1) card_Un_disjnt)
    apply blast
         apply blast
        apply (simp del: listPorts.simps add: disjnt_def)
        apply safe[1]
    apply clarsimp
    apply (subst (1 2) distinct_length_filter[symmetric], metis distinct_listPorts, metis distinct_listPorts)
  by (simp add: pgConstruct_ports del: listPorts.simps)

text\<open>Number of output ports matches number of output resource parallel parts\<close>
lemma pgConstruct_out_ports:
  assumes "pgDefined x"
    shows " length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x)))
          = length (parallel_parts (output x))"
  using assms
  apply (subst distinct_length_filter)
  using port_graph.ports_distinct port_graph_flow_def port_graph_flow_pgConstruct apply blast
  apply (subst pgConstruct_ports, assumption)
  apply (simp del: listPorts.simps add: Int_Un_distrib)
    apply (subst (1) card_Un_disjnt)
    apply blast
         apply blast
        apply (simp del: listPorts.simps add: disjnt_def)
        apply safe[1]
    apply clarsimp
    apply (subst (1 2) distinct_length_filter[symmetric], metis distinct_listPorts, metis distinct_listPorts)
  by (simp add: pgConstruct_ports del: listPorts.simps)

text\<open>Nodes of the constructed port graph correspond (even in order) to primitives of the process\<close>
lemma pgConstruct_nodes:
  assumes "pgDefined x"
    shows " pg_nodes (pgConstruct x)
          = map (\<lambda>(n, ins, outs, l, m).
                  Node n (NodePrimitive l m) ( listPorts 0 In (parallel_parts ins)
                                             @ listPorts 0 Out (parallel_parts outs)))
                (namedPrimitives x)"
  using assms by (induct x) (simp_all add: Ball_def)

subsection\<open>Construction Equivalences\<close>

text\<open>
  Constructing port graphs from process compositions allows us to take the notion of port graph
  equivalence and apply it to processes.
  We expect usual process laws from the literature to be equivalences (or even equalities) of the
  constructed port graphs.
\<close>

text\<open>Swapping one way has as sequential inverse swapping the other way\<close>
lemma pgConstruct_swap_inverse:
  "pgConstruct (Seq (Swap x y) (Swap y x)) \<approx> pgConstruct (Identity (x \<odot> y))"
  by (simp only: pgConstruct.simps qualifyPortGraph_swapPortGraph seqPortGraphs_swap_inverse parallel_parts_par)

text\<open>Identity is its own sequential inverse\<close>
lemma pgConstruct_id_inverse:
  "pgConstruct (Seq (Identity x) (Identity x)) = pgConstruct (Identity x)"
  by (simp only: pgConstruct.simps qualifyPortGraph_idPortGraph seqPortGraphs_id_inverse)

text\<open>Parallel composition of identities is equivalent to the combined identity\<close>
lemma pgConstruct_id_merge:
  "pgConstruct (Par (Identity x) (Identity y)) \<approx> pgConstruct (Identity (x \<odot> y))"
  by (simp only: pgConstruct.simps qualifyPortGraph_idPortGraph juxtapose_id_merge parallel_parts_par)

text\<open>Identity on the empty resource is unit of parallel composition\<close>
lemma pgConstruct_par_unit_pgEquiv:
  assumes "pgDefined x"
  shows pgConstruct_par_unitL_pgEquiv: "pgConstruct (Par (Identity Empty) x) \<approx> pgConstruct x"
    and pgConstruct_par_unitR_pgEquiv: "pgConstruct (Par x (Identity Empty)) \<approx> pgConstruct x"
   apply (simp only: pgConstruct.simps qualifyPortGraph_idPortGraph parallel_parts_simps)
   apply (subst juxtapose_unitL)
  apply (rule pgEquiv_qualifyPortGraph)
  using port_graph_flow_pgConstruct assms port_graph_flow.axioms(1) apply blast
   apply (simp only: pgConstruct.simps qualifyPortGraph_idPortGraph parallel_parts_simps)
   apply (subst juxtapose_unitR)
  apply (rule pgEquiv_qualifyPortGraph)
  using port_graph_flow_pgConstruct assms port_graph_flow.axioms(1) apply blast
  done

text\<open>Identity (on the relevant input or output resource) is unit of sequential composition\<close>
lemma pgConstruct_seq_unit_pgEquiv:
  assumes "pgDefined x"
  shows pgConstruct_seq_unitL_pgEquiv: "pgConstruct (Seq (Identity (input x)) x) \<approx> pgConstruct x"
    and pgConstruct_seq_unitR_pgEquiv: "pgConstruct (Seq x (Identity (output x))) \<approx> pgConstruct x"
   apply (simp only: pgConstruct.simps qualifyPortGraph_idPortGraph)
  apply (rule pgEquiv_trans)
    apply (rule seqPortGraphs_unitL_pgEquiv)
  using port_graph_flow_pgConstruct assms port_graph_flow_qualifyPortGraph apply fastforce
  using assms apply (fastforce simp add: pgConstruct_ports)
  using port_graph_flow_pgConstruct assms port_graph_flow.axioms pgEquiv_qualifyPortGraph apply fastforce
   apply (simp only: pgConstruct.simps qualifyPortGraph_idPortGraph)
  apply (rule pgEquiv_trans)
    apply (rule seqPortGraphs_unitR_pgEquiv)
  using port_graph_flow_pgConstruct assms port_graph_flow_qualifyPortGraph apply fastforce
  using assms apply (fastforce simp add: pgConstruct_ports)
  using port_graph_flow_pgConstruct assms port_graph_flow.axioms pgEquiv_qualifyPortGraph apply fastforce
  done

text\<open>Parallel composition is associative\<close>
lemma pgConstruct_Par_assoc:
  assumes "pgDefined x"
      and "pgDefined y"
      and "pgDefined z"
    shows "pgConstruct (Par (Par x y) z) \<approx> pgConstruct (Par x (Par y z))"
  unfolding pgConstruct.simps qualifyPortGraph_juxtapose
  apply (intro juxtapose_assoc_pgEquiv port_graph_qualifyPortGraph)
proof -
  show pg_x: "port_graph (pgConstruct x)"
   and "port_graph (pgConstruct x)"
    using assms port_graph_flow_pgConstruct port_graph_flow.axioms(1) by blast+
  show pg_y: "port_graph (pgConstruct y)"
   and "port_graph (pgConstruct y)"
    using assms port_graph_flow_pgConstruct port_graph_flow.axioms(1) by blast+
  show pg_z: "port_graph (pgConstruct z)"
   and "port_graph (pgConstruct z)"
    using assms port_graph_flow_pgConstruct port_graph_flow.axioms(1) by blast+
  show "pg_disjoint (qualifyPortGraph ParL (qualifyPortGraph ParL (pgConstruct x)))
     (qualifyPortGraph ParL (qualifyPortGraph ParR (pgConstruct y)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph ParL (qualifyPortGraph ParR (pgConstruct y)))
     (qualifyPortGraph ParR (pgConstruct z))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph ParL (qualifyPortGraph ParL (pgConstruct x)))
     (qualifyPortGraph ParR (pgConstruct z))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph ParL (pgConstruct x))
     (qualifyPortGraph ParR (qualifyPortGraph ParL (pgConstruct y)))"
    using qualifyPortGraph_apart by (metis process_inner.simps(24))
  show "pg_disjoint (qualifyPortGraph ParR (qualifyPortGraph ParL (pgConstruct y)))
     (qualifyPortGraph ParR (qualifyPortGraph ParR (pgConstruct z)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph ParL (pgConstruct x))
     (qualifyPortGraph ParR (qualifyPortGraph ParR (pgConstruct z)))"
    using qualifyPortGraph_apart by (metis process_inner.simps(24))
  show
    " qualifyPortGraph ParL (qualifyPortGraph ParL (pgConstruct x)) \<approx>
      qualifyPortGraph ParL (pgConstruct x)"
    using pg_x
    by (intro pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph)
  show
    " qualifyPortGraph ParL (qualifyPortGraph ParR (pgConstruct y)) \<approx>
      qualifyPortGraph ParR (qualifyPortGraph ParL (pgConstruct y))"
  proof -
    have "qualifyPortGraph ParL (qualifyPortGraph ParR (pgConstruct y)) \<approx> pgConstruct y"
      using pg_y
      by (metis pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph pgEquiv_trans)
    moreover have "qualifyPortGraph ParR (qualifyPortGraph ParL (pgConstruct y)) \<approx> pgConstruct y"
      using pg_y
      by (metis pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph pgEquiv_trans)
    ultimately show ?thesis
      using pgEquiv_sym pgEquiv_trans by blast
  qed
  show
    " qualifyPortGraph ParR (pgConstruct z) \<approx>
      qualifyPortGraph ParR (qualifyPortGraph ParR (pgConstruct z))"
    using pg_z
    by (intro pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph pgEquiv_sym)
qed

text\<open>Sequential composition is associative\<close>
lemma pgConstruct_Seq_assoc:
  assumes "pgDefined x"
      and "pgDefined y"
      and "pgDefined z"
    shows "pgConstruct (Seq (Seq x y) z) \<approx> pgConstruct (Seq x (Seq y z))"
  unfolding pgConstruct.simps qualifyPortGraph_seqPortGraphs
  apply (intro seqPortGraphs_assoc_pgEquiv port_graph_flow_qualifyPortGraph)
proof -
  show pgf_x: "port_graph_flow (pgConstruct x)"
   and "port_graph_flow (pgConstruct x)"
    using assms port_graph_flow_pgConstruct by blast+
  show pgf_y: "port_graph_flow (pgConstruct y)"
   and "port_graph_flow (pgConstruct y)"
    using assms port_graph_flow_pgConstruct by blast+
  show pgf_z: "port_graph_flow (pgConstruct z)"
   and "port_graph_flow (pgConstruct z)"
    using assms port_graph_flow_pgConstruct by blast+
  show "pg_disjoint (qualifyPortGraph SeqL (qualifyPortGraph SeqL (pgConstruct x)))
     (qualifyPortGraph SeqL (qualifyPortGraph SeqR (pgConstruct y)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph SeqL (qualifyPortGraph SeqR (pgConstruct y)))
     (qualifyPortGraph SeqR (pgConstruct z))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph SeqL (qualifyPortGraph SeqL (pgConstruct x)))
     (qualifyPortGraph SeqR (pgConstruct z))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph SeqL (pgConstruct x))
     (qualifyPortGraph SeqR (qualifyPortGraph SeqL (pgConstruct y)))"
    using qualifyPortGraph_apart by (metis process_inner.simps(1))
  show "pg_disjoint (qualifyPortGraph SeqR (qualifyPortGraph SeqL (pgConstruct y)))
     (qualifyPortGraph SeqR (qualifyPortGraph SeqR (pgConstruct z)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph SeqL (pgConstruct x))
     (qualifyPortGraph SeqR (qualifyPortGraph SeqR (pgConstruct z)))"
    using qualifyPortGraph_apart by (metis process_inner.simps(2))
  show
    " qualifyPortGraph SeqL (qualifyPortGraph SeqL (pgConstruct x)) \<approx>
      qualifyPortGraph SeqL (pgConstruct x)"
    using pgf_x
    by (intro port_graph_flow.axioms(1) pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph)
  show
    " qualifyPortGraph SeqL (qualifyPortGraph SeqR (pgConstruct y)) \<approx>
      qualifyPortGraph SeqR (qualifyPortGraph SeqL (pgConstruct y))"
  proof -
    have "qualifyPortGraph SeqL (qualifyPortGraph SeqR (pgConstruct y)) \<approx> pgConstruct y"
      using pgf_y
      by (metis pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph port_graph_flow.axioms(1) pgEquiv_trans)
    moreover have "qualifyPortGraph SeqR (qualifyPortGraph SeqL (pgConstruct y)) \<approx> pgConstruct y"
      using pgf_y
      by (metis pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph port_graph_flow.axioms(1) pgEquiv_trans)
    ultimately show ?thesis
      using pgEquiv_sym pgEquiv_trans by blast
  qed
  show
    " qualifyPortGraph SeqR (pgConstruct z) \<approx>
      qualifyPortGraph SeqR (qualifyPortGraph SeqR (pgConstruct z))"
    using pgf_z
    by (intro port_graph_flow.axioms(1) pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph pgEquiv_sym)
qed

text\<open>
  If parallel composition of sequential compositions is valid, then the interchanged variant is also
  valid.
  What is more important, when both are valid their port graphs are equivalent
\<close>
lemma
  "valid (Par (Seq x y) (Seq u v)) \<Longrightarrow> valid (Seq (Par x u) (Par y v))"
  by simp

lemma pgConstruct_interchange:
  assumes "pgDefined x"
      and "pgDefined y"
      and "pgDefined u"
      and "pgDefined v"
      and "valid (Par (Seq x y) (Seq u v))"
    shows "pgConstruct (Par (Seq x y) (Seq u v)) \<approx> pgConstruct (Seq (Par x u) (Par y v))"
  unfolding pgConstruct.simps
  unfolding qualifyPortGraph_juxtapose
  apply (subst (1 2) qualifyPortGraph_seqPortGraphs)
  apply (intro port_graph_par_seq_comm port_graph_flow_qualifyPortGraph)
proof -
  show pgf_x: "port_graph_flow (pgConstruct x)"
   and "port_graph_flow (pgConstruct x)"
    using assms port_graph_flow_pgConstruct by blast+
  show pgf_y: "port_graph_flow (pgConstruct y)"
   and "port_graph_flow (pgConstruct y)"
    using assms port_graph_flow_pgConstruct by blast+
  show pgf_u: "port_graph_flow (pgConstruct u)"
   and "port_graph_flow (pgConstruct u)"
    using assms port_graph_flow_pgConstruct by blast+
  show pgf_v: "port_graph_flow (pgConstruct v)"
   and "port_graph_flow (pgConstruct v)"
    using assms port_graph_flow_pgConstruct by blast+
  show "pg_disjoint (qualifyPortGraph ParL (qualifyPortGraph SeqL (pgConstruct x)))
     (qualifyPortGraph ParL (qualifyPortGraph SeqR (pgConstruct y)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph ParR (qualifyPortGraph SeqL (pgConstruct u)))
     (qualifyPortGraph ParR (qualifyPortGraph SeqR (pgConstruct v)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint
     (seqPortGraphs (qualifyPortGraph ParL (qualifyPortGraph SeqL (pgConstruct x)))
       (qualifyPortGraph ParL (qualifyPortGraph SeqR (pgConstruct y))))
     (seqPortGraphs (qualifyPortGraph ParR (qualifyPortGraph SeqL (pgConstruct u)))
       (qualifyPortGraph ParR (qualifyPortGraph SeqR (pgConstruct v))))"
    using qualifyPortGraph_apart
    by (metis process_inner.distinct(23) qualifyPortGraph_seqPortGraphs)
  show "pg_disjoint (qualifyPortGraph SeqL (qualifyPortGraph ParL (pgConstruct x)))
     (qualifyPortGraph SeqL (qualifyPortGraph ParR (pgConstruct u)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint (qualifyPortGraph SeqR (qualifyPortGraph ParL (pgConstruct y)))
     (qualifyPortGraph SeqR (qualifyPortGraph ParR (pgConstruct v)))"
    using qualifyPortGraph_apart by clarsimp
  show "pg_disjoint
     (juxtapose (qualifyPortGraph SeqL (qualifyPortGraph ParL (pgConstruct x)))
       (qualifyPortGraph SeqL (qualifyPortGraph ParR (pgConstruct u))))
     (juxtapose (qualifyPortGraph SeqR (qualifyPortGraph ParL (pgConstruct y)))
       (qualifyPortGraph SeqR (qualifyPortGraph ParR (pgConstruct v))))"
    using qualifyPortGraph_apart
    by (metis process_inner.distinct(1) qualifyPortGraph_juxtapose)
  show
    " qualifyPortGraph ParL (qualifyPortGraph SeqL (pgConstruct x)) \<approx>
      qualifyPortGraph SeqL (qualifyPortGraph ParL (pgConstruct x))"
    using pgf_x pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph port_graph_flow.axioms
    by (smt (verit, best) pgEquiv_sym pgEquiv_trans)
  show
    " qualifyPortGraph ParL (qualifyPortGraph SeqR (pgConstruct y)) \<approx>
      qualifyPortGraph SeqR (qualifyPortGraph ParL (pgConstruct y))"
    using pgf_y pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph port_graph_flow.axioms
    by (smt (verit, best) pgEquiv_sym pgEquiv_trans)
  show
    " qualifyPortGraph ParR (qualifyPortGraph SeqL (pgConstruct u)) \<approx>
      qualifyPortGraph SeqL (qualifyPortGraph ParR (pgConstruct u))"
    using pgf_u pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph port_graph_flow.axioms
    by (smt (verit, best) pgEquiv_sym pgEquiv_trans)
  show
    " qualifyPortGraph ParR (qualifyPortGraph SeqR (pgConstruct v)) \<approx>
      qualifyPortGraph SeqR (qualifyPortGraph ParR (pgConstruct v))"
    using pgf_v pgEquiv_qualifyPortGraph port_graph_qualifyPortGraph port_graph_flow.axioms
    by (smt (verit, best) pgEquiv_sym pgEquiv_trans)
  show
    " length (filter (\<lambda>x. port.side x = Out) (pg_ports (qualifyPortGraph ParL (qualifyPortGraph SeqL (pgConstruct x))))) =
      length (filter (\<lambda>x. port.side x = In) (pg_ports (qualifyPortGraph ParL (qualifyPortGraph SeqR (pgConstruct y)))))"
    using assms pgConstruct_in_ports pgConstruct_out_ports
    by (metis qualifyPortGraph_simps(4) valid.simps(2) valid.simps(3))
  show
    " length (filter (\<lambda>x. port.side x = Out) (pg_ports (qualifyPortGraph ParR (qualifyPortGraph SeqL (pgConstruct u))))) =
      length (filter (\<lambda>x. port.side x = In) (pg_ports (qualifyPortGraph ParR (qualifyPortGraph SeqR (pgConstruct v)))))"
    using assms pgConstruct_in_ports pgConstruct_out_ports
    by (metis qualifyPortGraph_simps(4) valid.simps(2) valid.simps(3))
  show "place_side p = In \<or> place_side p = Out"
   and "place_side p = In \<or> place_side p = Out"
   and "place_side p = In \<or> place_side p = Out"
   and "place_side p = In \<or> place_side p = Out"
    for p :: "(process_side, ('a, 'b) resource, process_inner) place"
    by (metis In_process_side_def Out_process_side_def process_side.exhaust)+
qed

text\<open>Swap can be passed sequentially through parallel composition, swapping its components in the process\<close>
lemma namesOfPlaces_image_Open [simp]: (* TODO move theorem *)
  "namesOfPlaces (OpenPort ` A) = {}"
  by (simp add: namesOfPlaces_def)

lemma namesOfPlaces_qualifyPlace [simp]: (* TODO move theorem *)
  "namesOfPlaces (qualifyPlace a ` A) = (#) a ` namesOfPlaces A"
  by (simp add: namesOfPlaces_def image_Collect)
     (metis (no_types, lifting) qualifyPlace_simps(1))

lemma namesOfPlaces_shiftOpenPlace [simp]: (* TODO move theorem *)
  "namesOfPlaces (shiftOpenPlace n ` A) = namesOfPlaces A"
  by (simp add: namesOfPlaces_def)
     (metis (no_types, lifting) shiftOpenPlace_ground(2))

lemma edgesSwapPre:
  assumes "pgDefined x"
      and "input x = b \<odot> a"
    shows
      " set (pg_edges (pgConstruct (Seq (Swap a b) x)))
      = (\<lambda>e. if place_open (edge_from e)
          then Edge
            (let p = place_port (edge_from e) in
              if port.index p < length (parallel_parts b)
                then OpenPort (Port (port.side p) (port.index p + length (parallel_parts a)) (port.label p))
                else OpenPort (Port (port.side p) (port.index p - length (parallel_parts b)) (port.label p)))
            (edge_to e)
          else e) ` qualifyEdge SeqR ` set (pg_edges (pgConstruct x))"
proof -
  have pgf_swap: "port_graph_flow (pgConstruct (Swap a b))"
    by (simp del: pgConstruct.simps add: port_graph_flow_pgConstruct)
  then interpret swap: port_graph_flow "pgConstruct (Swap a b)" .

  have pgf_x: "port_graph_flow (pgConstruct x)"
    using assms by (simp add: port_graph_flow_pgConstruct)
  then interpret x: port_graph_flow "pgConstruct x" .

  have pgf_seq: "port_graph_flow (pgConstruct (Seq (Swap a b) x))"
    using assms by (simp del: pgConstruct.simps add: port_graph_flow_pgConstruct)
  then interpret seq: port_graph_flow "pgConstruct (Seq (Swap a b) x)" .

  note [simp del] = listPorts.simps

  show ?thesis
    sorry
qed

lemma edgesSwapPost:
  assumes "pgDefined x"
      and "output x = a \<odot> b"
    shows
      " set (pg_edges (pgConstruct (Seq x (Swap a b))))
      = (\<lambda>e. if place_open (edge_to e)
          then Edge
            (edge_from e)
            (let p = place_port (edge_to e) in
              if port.index p < length (parallel_parts a)
                then OpenPort (Port (port.side p) (port.index p + length (parallel_parts b)) (port.label p))
                else OpenPort (Port (port.side p) (port.index p - length (parallel_parts a)) (port.label p)))
          else e) ` qualifyEdge SeqL ` set (pg_edges (pgConstruct x))"
proof -
  have pgf_swap: "port_graph_flow (pgConstruct (Swap a b))"
    by (simp del: pgConstruct.simps add: port_graph_flow_pgConstruct)
  then interpret swap: port_graph_flow "pgConstruct (Swap a b)" .

  have pgf_x: "port_graph_flow (pgConstruct x)"
    using assms by (simp add: port_graph_flow_pgConstruct)
  then interpret x: port_graph_flow "pgConstruct x" .

  have pgf_seq: "port_graph_flow (pgConstruct (Seq x (Swap a b)))"
    using assms by (simp del: pgConstruct.simps add: port_graph_flow_pgConstruct)
  then interpret seq: port_graph_flow "pgConstruct (Seq x (Swap a b))" .

  note [simp del] = listPorts.simps

  show ?thesis
    sorry
qed

lemma pgConstruct_swap_natural:
  assumes "valid x"
      and "valid y"
      and "pgDefined x"
      and "pgDefined y"
    shows "pgConstruct (Seq (Swap (input x) (input y)) (Par y x)) \<approx> pgConstruct (Seq (Par x y) (Swap (output x) (output y)))"
proof (rule pgEquivI_ex)
  have pgf_x: "port_graph_flow (pgConstruct x)"
    using assms by (simp add: port_graph_flow_pgConstruct)
  then interpret x: port_graph_flow "pgConstruct x" .

  have pgf_y: "port_graph_flow (pgConstruct y)"
    using assms by (simp add: port_graph_flow_pgConstruct)
  then interpret y: port_graph_flow "pgConstruct y" .

  show pg_LHS: "port_graph (pgConstruct (Seq (Swap (input x) (input y)) (Par y x)))"
    using port_graph_flow.axioms(1) port_graph_flow_pgConstruct assms(3,4)
    by (metis pgDefined.simps(3,4,5))
  show pg_RHS: "port_graph (pgConstruct (Seq (Par x y) (Swap (output x) (output y))))"
    using port_graph_flow.axioms(1) port_graph_flow_pgConstruct assms(3,4)
    by (metis pgDefined.simps(3,4,5))
  show
    " set (pg_ports (pgConstruct (Seq (Swap (input x) (input y)) (Par y x))))
    = set (pg_ports (pgConstruct (Seq (Par x y) (Swap (output x) (output y)))))"
    using assms by (subst (1 2) pgConstruct_ports) simp_all

  let ?f = "\<lambda>ps. if 1 < length ps then SeqL # (if ps ! 1 = ParL then ParR else if ps ! 1 = ParR then ParL else ps ! 1) # drop 2 ps else ps"
  let ?g = "\<lambda>ps. if 1 < length ps then SeqR # (if ps ! 1 = ParL then ParR else if ps ! 1 = ParR then ParL else ps ! 1) # drop 2 ps else ps"

  show "\<exists>f g. pgEquiv_witness f g
    (pgConstruct (Seq (Swap (input x) (input y)) (Par y x)))
    (pgConstruct (Seq (Par x y) (Swap (output x) (output y))))"
  proof (intro exI pgEquiv_witnessI)
    show
      " renameNode ?f ` set (pg_nodes (pgConstruct (Seq (Swap (input x) (input y)) (Par y x))))
      = set (pg_nodes (pgConstruct (Seq (Par x y) (Swap (output x) (output y)))))"
      by (simp add: image_Un image_comp qualifyNode_def del: One_nat_def) blast
    show
      " set (pg_nodes (pgConstruct (Seq (Swap (input x) (input y)) (Par y x))))
      = renameNode ?g ` set (pg_nodes (pgConstruct (Seq (Par x y) (Swap (output x) (output y)))))"
      by (simp add: image_Un image_comp qualifyNode_def del: One_nat_def) blast

    (* Generally true but quite specific simplifications for this proof *)
    have namesOfPlaces_shift_other [simp]:
      " namesOfPlaces ((\<lambda>x. shiftOpenPlace n (f x)) ` A)
      = namesOfPlaces (f ` A)" for n f A
      by (metis image_image namesOfPlaces_shiftOpenPlace)
    have namesOfPlaces_qualify_f [simp]:
      " namesOfPlaces ((\<lambda>x. qualifyPlace a (f x)) ` A)
      = (#) a ` namesOfPlaces (f ` A)" for a f A
      by (metis image_image namesOfPlaces_qualifyPlace)
    have namesOfPlaces_open_f [simp]:
      "namesOfPlaces ((\<lambda>x. OpenPort (f x)) ` A) = {}" for f A
      by (simp add: namesOfPlaces_def)
    have renamePlace_qualifyPlace [simp]:
      "renamePlace f (qualifyPlace a (g x)) = renamePlace (f \<circ> (#) a) (g x)" for f g a x
      by (simp add: qualifyPlace_rename)
    have renameEdge_qualifyEdge [simp]:
      "renameEdge f (qualifyEdge a (g x)) = renameEdge (f \<circ> (#) a) (g x)" for f g a x
      by (simp add: qualifyEdge_rename)
    have renamePlace_to_edgesByOpenFrom [simp]:
      " Mapping.map_values (\<lambda>k. map (\<lambda>x. renamePlace f (edge_to x))) (edgesByOpenFrom es)
      = Mapping.map_values (\<lambda>k. map edge_to) (edgesByOpenFrom (map (renameEdge f) es))" for f es
      apply (induct es)
       apply simp
      apply simp
      apply safe
        apply (simp add: Mapping.map_default_def map_entry_code lookup_default')
      apply (smt (z3) default_def keys_map_values list.simps(8) list.simps(9) lookup_default_map_values map_values_update renameEdge_simps(3))
       apply blast
      apply blast
      done
    have renamePlace_from_edgesByOpenTo [simp]:
      " Mapping.map_values (\<lambda>k. map (\<lambda>x. renamePlace f (edge_from x))) (edgesByOpenTo es)
      = Mapping.map_values (\<lambda>k. map edge_from) (edgesByOpenTo (map (renameEdge f) es))" for f es
      apply (induct es)
       apply simp
      apply simp
      apply safe
        apply (simp add: Mapping.map_default_def map_entry_code lookup_default')
      apply (smt (z3) default_def keys_map_values list.simps(8) list.simps(9) lookup_default_map_values map_values_update renameEdge_simps(2))
       apply blast
      apply blast
      done

    note [simp] =
      renameEdge_qualifyEdge[of _ _ "\<lambda>x. x"]
      map2_map_each[where gl = OpenPort and gr = OpenPort]

    note [simp del] = listPorts.simps pgConstruct.simps

    have "pgDefined (Par y x)" "input (Par y x) = input y \<odot> input x"
      using assms by simp_all
    note edge_set_LHS = edgesSwapPre[OF this]

    have "pgDefined (Par x y)" "output (Par x y) = output x \<odot> output y"
      using assms by simp_all
    note edge_set_RHS = edgesSwapPost[OF this]

    have
      " renameEdge ?f ` set (pg_edges (pgConstruct (Seq (Swap (input x) (input y)) (Par y x))))
      = set (pg_edges (pgConstruct (Seq (Par x y) (Swap (output x) (output y)))))"
    proof safe
      fix e
      assume e: "e \<in> set (pg_edges (pgConstruct (Seq (Swap (input x) (input y)) (Par y x))))"

      consider "place_open (edge_from e)" | "place_ground (edge_from e)"
        by fastforce
      then consider
          e' where "place_open (edge_from e)"
               and "e' \<in> set (pg_edges (pgConstruct (Par y x)))"
               and "port.index (place_port (edge_from e')) < length (Resource.parallel_parts (input y))"
               and "edge_from e = OpenPort (Port
                      (port.side (place_port (edge_from e')))
                      (port.index (place_port (edge_from e')) + length (Resource.parallel_parts (input x)))
                      (port.label (place_port (edge_from e'))))"
               and "edge_to e = qualifyPlace SeqR (edge_to e')"
        | e' where "place_open (edge_from e)"
               and "e' \<in> set (pg_edges (pgConstruct (Par y x)))"
               and "\<not> port.index (place_port (edge_from e')) < length (Resource.parallel_parts (input y))"
               and "edge_from e = OpenPort (Port
                      (port.side (place_port (edge_from e')))
                      (port.index (place_port (edge_from e')) - length (Resource.parallel_parts (input y)))
                      (port.label (place_port (edge_from e'))))"
               and "edge_to e = qualifyPlace SeqR (edge_to e')"
        | e' where "place_ground (edge_from e)" and "e = qualifyEdge SeqR e'" and "e' \<in> set (pg_edges (pgConstruct (Par y x)))"
      proof cases
        case 1
        then obtain e' where e':
          "e = Edge
            (if port.index (place_port (edge_from e')) < length (Resource.parallel_parts (input y))
             then OpenPort
                   (Port (port.side (place_port (edge_from e')))
                     (port.index (place_port (edge_from e')) + length (Resource.parallel_parts (input x)))
                     (port.label (place_port (edge_from e'))))
             else OpenPort
                   (Port (port.side (place_port (edge_from e')))
                     (port.index (place_port (edge_from e')) - length (Resource.parallel_parts (input y)))
                     (port.label (place_port (edge_from e')))))
            (edge_to e')"
          "e' \<in> qualifyEdge SeqR ` set (pg_edges (pgConstruct (Par y x))) \<inter> {x. place_open (edge_from x)}"
          using e edge_set_LHS by (smt (verit, ccfv_SIG) Int_Collect image_iff)

        show ?thesis
        proof (cases "port.index (place_port (edge_from e')) < length (Resource.parallel_parts (input y))")
             case True  then show ?thesis using e' that(1) by clarsimp
        next case False then show ?thesis using e' that(2) by clarsimp
        qed
      next
        case 2
        then show ?thesis
          using that(3) e edge_set_LHS
          by (smt (verit, best) edge.sel(1) image_iff place.disc(2))
      qed
      note from_cases = this

      then show "renameEdge ?f e \<in> set (pg_edges (pgConstruct (Seq (Par x y) (Swap (output x) (output y)))))"
      proof cases
        case 1
        then show ?thesis
          sorry
      next
        case 2
        then show ?thesis
          sorry
      next
        case 3
        then show ?thesis
          unfolding edge_set_RHS
          sorry
      qed
    next
      fix e
      assume e: "e \<in> set (pg_edges (pgConstruct (Seq (Par x y) (Swap (output x) (output y)))))"

      show "e \<in> renameEdge ?f ` set (pg_edges (pgConstruct (Seq (Swap (input x) (input y)) (Par y x))))"
        sorry
    qed

    oops (* TODO perhaps it would be easier to prove at the general port graph level *)

subsection\<open>Construction Node Flow\<close>

text\<open>Port graphs constructed for compositions have acyclic node flow\<close>

lemma primitivePortGraph_edge_open:
  assumes "e \<in> set (pg_edges (pgConstruct (Primitive a b l m)))"
  obtains "place_open (edge_from e)" | "place_open (edge_to e)"
  using assms nodePortGraph_edge_open pgConstruct.simps(1) by metis

lemma acyclic_empty [simp]:
  "acyclic {}"
  by (simp add: acyclic_def)

lemma acyclicP_empty [simp]:
  assumes "\<And>x y. \<not> R x y"
    shows "acyclicP R"
  using assms by simp

lemma node_flow_no_nodes [simp]:
  assumes "pg_nodes G = []"
    shows "\<not> node_flow G a b"
  using assms by (simp add: node_flow.simps)

lemma acyclic_pgConstruct:
  assumes "pgDefined x"
    shows "acyclicP (node_flow (pgConstruct x))"
  oops (* TODO *)

subsection\<open>Construction Nodes\<close>

text\<open>
  Port graph nodes correspond to the primitive actions.
  In the statement we remove the node names, since the list of primitives does not keep information
  about where in the composition the action comes from.
  Note that, since we use lists, the order and number match.
\<close>
lemma pgConstruct_nodes_are_primitives:
  assumes "pgDefined x"
    shows
      " map (\<lambda>n. Node [] (node_label n) (node_ports n)) (pg_nodes (pgConstruct x)) =
        map (\<lambda>(ins, outs, l, m).
                Node [] (NodePrimitive l m) (parallelPorts 0 In ins @ parallelPorts 0 Out outs))
            (primitives x)"
  using assms by (induct x) (simp_all add: comp_def)

subsection\<open>Construction Identity Characterisation\<close>

text\<open>
  Any process that can be validly self-composed in sequence and whose valid sequential composition
  to any other process from either side results in an equivalent port graph must have port graph
  equivalent to the identity port graph.

  There are two variants of the theorem, one for identity on input or output requiring only one of
  pre-/post-composition assumptions.

  These characterise identity-like processes on input (domain) and output (codomain).
\<close>

lemma pgConstruct_ide_input:
  assumes "pgDefined x"
      and "valid (Seq x x)"
      and "\<And>f. \<lbrakk>pgDefined f; valid (Seq f x)\<rbrakk> \<Longrightarrow> pgConstruct (Seq f x) \<approx> pgConstruct f"
    shows "pgConstruct x \<approx> pgConstruct (Identity (input x))"
proof -
  have "pgConstruct x \<approx> pgConstruct (Seq (Identity (input x)) x)"
    using assms(1) pgConstruct_seq_unitL_pgEquiv pgEquiv_sym by blast
  also have "... \<approx> pgConstruct (Identity (input x))"
    using assms(2,3) by (meson pgDefined.simps(2) output.simps(6) valid.simps(2) valid.simps(6))
  finally show "pgConstruct x \<approx> pgConstruct (Identity (input x))" .
qed

lemma pgConstruct_ide_output:
  assumes "pgDefined x"
      and "valid (Seq x x)"
      and "\<And>f. \<lbrakk>pgDefined f; valid (Seq x f)\<rbrakk> \<Longrightarrow> pgConstruct (Seq x f) \<approx> pgConstruct f"
    shows "pgConstruct x \<approx> pgConstruct (Identity (output x))"
proof -
  have "pgConstruct x \<approx> pgConstruct (Seq x (Identity (output x)))"
    using assms(1) pgConstruct_seq_unitR_pgEquiv pgEquiv_sym by blast
  also have "... \<approx> pgConstruct (Identity (output x))"
    using assms(2,3) by (metis pgDefined.simps(2) input.simps(6) valid.simps(2) valid.simps(6))
  finally show "pgConstruct x \<approx> pgConstruct (Identity (output x))" .
qed

lemma (* TODO any process with PG equivalent to identity functions like it *)
  fixes x :: "('a, 'b, 'l, 'm) process"
  assumes "pgDefined x"
      and "valid x"
      and "pgConstruct x \<approx> pgConstruct (Identity (output x))"
    shows "\<And>f. \<lbrakk>pgDefined f; valid (Seq x f)\<rbrakk> \<Longrightarrow> pgConstruct (Seq x f) \<approx> pgConstruct f"
proof -
  fix y :: "('a, 'b, 'l, 'm) process"
  assume y: "pgDefined y"

  have "port_graph (pgConstruct x)"
    using assms(1,2) port_graph_flow_pgConstruct port_graph_flow.axioms(1) by blast
  moreover have "port_graph (pgConstruct (Identity (output x)))"
    using port_graph_flow_pgConstruct pgDefined.simps(2) port_graph_flow.axioms(1) by blast
  ultimately obtain f g
    where ports: "set (pg_ports (pgConstruct x)) = set (pg_ports (pgConstruct (Identity (output x))))"
      and witness: "pgEquiv_witness f g (pgConstruct x) (pgConstruct (Identity (output x)))"
    using assms(3) pgEquivE by auto

  show "pgConstruct (Seq x y) \<approx> pgConstruct y"
  proof (intro pgEquivI pgEquiv_witnessI)
    show "port_graph (pgConstruct (Seq x y))"
      using assms(1,2) y port_graph_flow_pgConstruct pgDefined.simps(4) port_graph_flow.axioms(1) by metis
    show "port_graph (pgConstruct y)"
      using y port_graph_flow_pgConstruct port_graph_flow.axioms(1) by blast
    oops

subsection\<open>Copyable Resources are Comonoids\<close>

text\<open>
  Copyable resources are commutative comonoids thanks to duplication and erasing:
  \<^item> Erasing either result after duplication is identity (unital)
  \<^item> In duplication followed by identity and another duplication (in parallel), the order of the
    second component does not matter (associativity)
  \<^item> Swapping after duplication has no effect
\<close>
lemma
  shows pgConstruct_duplicate_eraseL:
    " pgConstruct (Seq (Duplicate x) (Par (Erase x) (Identity (Copyable x))))
    = pgConstruct (Identity (Copyable x))"
    and pgConstruct_duplicate_eraseR:
    " pgConstruct (Seq (Duplicate x) (Par (Identity (Copyable x)) (Erase x)))
    = pgConstruct (Identity (Copyable x))"
    and pgConstruct_duplicate_assoc:
    " pgConstruct (Seq (Duplicate x) (Par (Identity (Copyable x)) (Duplicate x)))
    = pgConstruct (Seq (Duplicate x) (Par (Duplicate x) (Identity (Copyable x))))"
  unfolding pgConstruct.simps parallel_parts_simps qualifyPortGraph_forkPortGraph
            qualifyPortGraph_endPortGraph qualifyPortGraph_idPortGraph qualifyPortGraph_juxtapose
  by (rule forkPortGraph_unitL forkPortGraph_unitR forkPortGraph_assoc)+

lemma pgConstruct_duplicate_swap:
  " pgConstruct (Seq (Duplicate x) (Swap (Copyable x) (Copyable x)))
  \<approx> pgConstruct (Duplicate x)"
  using forkPortGraph_comm
  by (simp only: pgConstruct.simps qualifyPortGraph_swapPortGraph qualifyPortGraph_forkPortGraph parallel_parts_simps)

text\<open>
  Repatable process resources are commutative comonoids thanks to repeating and closing:
  \<^item> Closing either result after repeating is identity (unital)
  \<^item> In repeating followed by identity and another repeating (in parallel), the order of the
    second component does not matter (associativity)
  \<^item> Swapping after repeating has no effect
\<close>
lemma
  shows pgConstruct_repeat_closeL:
    " pgConstruct (Seq (Repeat x y) (Par (Close x y) (Identity (Repeatable x y))))
    = pgConstruct (Identity (Repeatable x y))"
    and pgConstruct_repeat_closeR:
    " pgConstruct (Seq (Repeat x y) (Par (Identity (Repeatable x y)) (Close x y)))
    = pgConstruct (Identity (Repeatable x y))"
    and pgConstruct_repeat_assoc:
    " pgConstruct (Seq (Repeat x y) (Par (Identity (Repeatable x y)) (Repeat x y)))
    = pgConstruct (Seq (Repeat x y) (Par (Repeat x y) (Identity (Repeatable x y))))"
  unfolding pgConstruct.simps parallel_parts_simps qualifyPortGraph_forkPortGraph
            qualifyPortGraph_endPortGraph qualifyPortGraph_idPortGraph qualifyPortGraph_juxtapose
  by (rule forkPortGraph_unitL forkPortGraph_unitR forkPortGraph_assoc)+

lemma pgConstruct_repeat_swap:
  " pgConstruct (Seq (Repeat x y) (Swap (Repeatable x y) (Repeatable x y)))
  \<approx> pgConstruct (Repeat x y)"
  using forkPortGraph_comm
  by (simp only: pgConstruct.simps qualifyPortGraph_swapPortGraph qualifyPortGraph_forkPortGraph parallel_parts_simps)

end
