theory GraphicalLinearity
  imports
    ProcessPortGraph
    ProcessPG_Util
begin

section\<open>Graphical Linearity\<close>

text\<open>
  We use port graphs constructed from process compositions to verify process linearity.
  Because port graphs are only constructed for sequential and parallel compositions, these facts
  only extend to those.

  By linearity we mean that every linear resource has a known and singular origin (composition input
  or action output) and it has a known and singular destination (composition output or action input).
  Additionally, we can show that copyable atoms and repeatable processes may have any number of
  destinations (including zero) but they still have a singular origin.

  This proof complements our relation of process compositions to deductions of (intuitionistic)
  linear logic, done for all compositions in a separate session.
  While that work demonstrates compositions are linear by appeal to linear logic, this proof talks
  concretely about properties of connections between actions.

  We prove this as a number of lemmas for the different cases which are then put together at the end.
\<close>

text\<open>First, the very useful fact that process port graphs only involve two sides\<close>
lemma process_side_filter_simps [simp]:
  "(\<lambda>s :: process_side. if s = In \<or> s = Out then 0 else f s) = (\<lambda>s. 0)"
  by (metis In_process_side_def Out_process_side_def process_side.exhaust)

text\<open>
  The origin and destination of every edge have the same label, except for turning a repeatably
  executable resource into a single-use one
\<close>
lemma pgConstruct_edge_carries_label:
    fixes proc :: "('a, 'b, 'l, 'm) process"
  assumes "pgDefined proc"
      and "e \<in> set (pg_edges (pgConstruct proc))"
  obtains "port.label (place_port (edge_from e)) = port.label (place_port (edge_to e))"
  | x y where "port.label (place_port (edge_from e)) = Repeatable x y" and "port.label (place_port (edge_to e)) = Executable x y"
  | "port.label (place_port (edge_to e)) = Anything"
proof -
  have
    " port.label (place_port (edge_from e)) = port.label (place_port (edge_to e))
    \<or> (\<exists>x y. port.label (place_port (edge_from e)) = Repeatable x y \<and> port.label (place_port (edge_to e)) = Executable x y)
    \<or> port.label (place_port (edge_to e)) = Anything"
    using assms
  proof (induct proc arbitrary: e)
    case (Primitive x1 x2a x3 x4)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Identity x)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Seq x1 x2)

    have pgf1: "port_graph_flow (pgConstruct x1)"
      using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x1: port_graph_flow "pgConstruct x1" .
    have pgf2: "port_graph_flow (pgConstruct x2)"
      using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x2: port_graph_flow "pgConstruct x2" .

    note port_graph_flow_qualifyPortGraph[OF pgf1]
         port_graph_flow_qualifyPortGraph[OF pgf2]
    moreover have "e \<in> set (pg_edges (seqPortGraphs (qualifyPortGraph SeqL (pgConstruct x1)) (qualifyPortGraph SeqR (pgConstruct x2))))"
      using Seq.prems by simp
    ultimately show ?case
    proof (cases rule: seqPortGraphs_edge_cases)
      case Stitch
      then obtain a b and p :: "(process_side, ('a,'b) resource) port" where
        "edge_from e = qualifyPlace SeqL (edge_from a)" "a \<in> set (pg_edges (pgConstruct x1))"
        "edge_to e = qualifyPlace SeqR (edge_to b)" "b \<in> set (pg_edges (pgConstruct x2))"
        "edge_to a = OpenPort (portSetSide Out p)" "edge_from b = OpenPort (portSetSide In p)"
        "port.side p = Out"
        apply (elim seqInterfaceEdges_setD)
        apply clarsimp
        by (metis place.disc(4) qualifyPlace_simps(2) qualifyPlace_simps(4))
      then show ?thesis
        apply (cases "port.label (place_port (edge_from a)) = port.label (place_port (edge_to a))")
        apply simp
        using Seq.hyps(2)[of b]
        apply (metis Seq.prems(1) pgDefined.simps(4) place_port.simps(2) portSetSide_label)
        apply (rule disjI2)
        using Seq.hyps(1)[of a] Seq.prems(1,2) apply (clarsimp del: disjCI)
        apply (cut_tac Seq.hyps(2)[of b])
        apply (erule disjE)
        apply (metis place_port.simps(2) portSetSide_label resource_neq(21))
        apply (metis place_port.simps(2) portSetSide_label resource_neq(11))
           apply clarsimp
        using Seq.prems(1) apply simp
        done
    next
      case L
      then obtain e' where "e = qualifyEdge SeqL e'" and "e' \<in> set (pg_edges (pgConstruct x1))"
        by clarsimp
      then show ?thesis
        using Seq.hyps(1)[of e'] Seq.prems(1,2) by simp
    next
      case (R e')
      then obtain e'' where "e' = qualifyEdge SeqR e''" and "e'' \<in> set (pg_edges (pgConstruct x2))"
        by clarsimp
      then show ?thesis
        using Seq.hyps(2)[of e''] Seq.prems(1,2) R(3) by simp
    qed
  next
    case (Swap x1 x2a)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip parallel_parts_par)
      done
  next
    case (Par x1 x2)
    then show ?case
      apply simp
      apply (elim disjE conjE)
      apply (clarsimp del: disjCI)
      apply (clarsimp del: disjCI)
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
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Erase x)
    then show ?case by simp
  next
    case (Represent x)
    then show ?case by simp
  next
    case (Apply x1 x2a)
    then show ?case by simp
  next
    case (Repeat x1 x2a)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Close x1 x2a)
    then show ?case by simp
  next
    case (Once x1 x2a)
    then show ?case by (simp del: parallelPorts.simps) blast
  next
    case (Forget x)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  qed
  then show ?thesis
    using that by blast
qed

text\<open>Any open port with two distinct edges touching it (and thus more than one destination) must carry a copyable resource\<close>
lemma pgConstruct_edge_copy_open:
  fixes x :: "('a, 'b, 'l, 'm) process"
  assumes "pgDefined x"
      and "p \<in> set (pgraphPlaces (pgConstruct x))"
      and "e1 \<in> set (pg_edges (pgConstruct x))"
      and "edge_from e1 = p"
      and "e2 \<in> set (pg_edges (pgConstruct x))"
      and "edge_from e2 = p"
      and "e1 \<noteq> e2"
      and "place_open p"
    shows "(\<exists>a. port.label (place_port p) = Copyable a) \<or> (\<exists>a b. port.label (place_port p) = Repeatable a b)"
proof -
  show ?thesis
    using assms
  proof (induct x arbitrary: p e1 e2)
    case (Primitive x1 x2a x3 x4)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Identity x)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Seq x1 x2)
    (* Both edges start at and open input, so they must be at least partly in x1.
       If they are both fully in x1 then it's by inductive hypothesis.
       If either is stitched but their left parts have distinct destinations then it's by inductive hypothesis.
       If either is stitched and their left parts have equal destinations then we must check right parts as well.
       If both were stitched (on the same port) then their right parts have distinct destinations and it's by other inductive hypothesis.
       If only one is stitched but its left side goes to the same destination as the unstitched then we should have a contradiction:
       \<rightarrow> If two edges go to the same open output then they will get equally stitched to something and originals are removed.
     *)

    have "port_graph_flow (pgConstruct (Seq x1 x2))"
      using Seq.prems(1,2) port_graph_flow_pgConstruct by blast
    then interpret x1x2: port_graph_flow "pgConstruct (Seq x1 x2)" .
    have pgf1: "port_graph_flow (pgConstruct x1)"
      using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x1: port_graph_flow "pgConstruct x1" .
    have pgf2: "port_graph_flow (pgConstruct x2)"
      using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x2: port_graph_flow "pgConstruct x2" .

    consider
    \<comment> \<open>The edges are in some combination of left side or stitch, neither is fully right side\<close>
              "e1 \<in> qualifyEdge SeqL ` set (pg_edges (pgConstruct x1))" and "\<not> toOpenOut e1"
          and "e2 \<in> qualifyEdge SeqL ` set (pg_edges (pgConstruct x1))" and "\<not> toOpenOut e2"
      | e2a e2b and port2 :: "(process_side, ('a, 'b) resource) port"
        where "e1 \<in> qualifyEdge SeqL ` set (pg_edges (pgConstruct x1))" and "\<not> toOpenOut e1"
          and "e2a \<in> set (pg_edges (pgConstruct x1))" and "e2b \<in> set (pg_edges (pgConstruct x2))"
          and "edge_to e2a = OpenPort (portSetSide Out port2)" and "edge_from e2b = OpenPort (portSetSide In port2)"
          and "port.side port2 = Out"
          and "edge_from e2 = qualifyPlace SeqR (edge_from e2a)" and "edge_to e2 = qualifyPlace SeqR (edge_to e2b)"
      | e1a e1b and port1 :: "(process_side, ('a, 'b) resource) port"
        where "e2 \<in> qualifyEdge SeqL ` set (pg_edges (pgConstruct x1))" and "\<not> toOpenOut e2"
          and "e1a \<in> set (pg_edges (pgConstruct x1))" and "e1b \<in> set (pg_edges (pgConstruct x2))"
          and "edge_to e1a = OpenPort (portSetSide Out port1)" and "edge_from e1b = OpenPort (portSetSide In port1)"
          and "port.side port1 = Out"
          and "edge_from e1 = qualifyPlace SeqR (edge_from e1a)" and "edge_to e1 = qualifyPlace SeqR (edge_to e1b)"
      | e1a e1b e2a e2b and port1 port2 :: "(process_side, ('a, 'b) resource) port"
        where "e1a \<in> set (pg_edges (pgConstruct x1))" and "e1b \<in> set (pg_edges (pgConstruct x2))"
          and "edge_to e1a = OpenPort (portSetSide Out port1)" and "edge_from e1b = OpenPort (portSetSide In port1)"
          and "port.side port1 = Out"
          and "edge_from e1 = qualifyPlace SeqL (edge_from e1a)" and "edge_to e1 = qualifyPlace SeqR (edge_to e1b)"
          and "e2a \<in> set (pg_edges (pgConstruct x1))" and "e2b \<in> set (pg_edges (pgConstruct x2))"
          and "edge_to e2a = OpenPort (portSetSide Out port2)" and "edge_from e2b = OpenPort (portSetSide In port2)"
          and "port.side port2 = Out"
          and "edge_from e2 = qualifyPlace SeqL (edge_from e2a)" and "edge_to e2 = qualifyPlace SeqR (edge_to e2b)"
    proof -
      show ?thesis
        \<comment> \<open>This really just gets all nine cases and massages each into the right form or shows it's a contradiction\<close>
        using Seq.prems(3,4,5,6,8)
        apply (simp del: seqPortGraphs.simps)
        apply (subst (asm) (1 2) seqPortGraphs_flow_edges[OF port_graph_flow_qualifyPortGraph[OF pgf1] port_graph_flow_qualifyPortGraph[OF pgf2]])
        apply (clarsimp simp del: seqInterfaceEdges.simps)
        apply (elim disjE seqInterfaceEdges_setD conjE)
        apply clarsimp
        using that(4) apply (metis place.disc(4) portSetSide_same qualifyPlace_simps(2,4))
        apply clarsimp
        using that(3) toOpenOut_qualifyEdge apply (metis (no_types, lifting) imageI place.disc(4) portSetSide_same qualifyPlace_simps(2,4))
        apply (metis fromOpenInI pgf1 port_graph_flow.edge_from_open port_graph_flow_qualifyPortGraph)
        apply clarsimp
        using that(2) toOpenOut_qualifyEdge apply (metis (no_types, lifting) imageI place.disc(4) portSetSide_same qualifyPlace_simps(2,4))
        apply clarsimp
        apply (metis (mono_tags, lifting) place_open_def place_port.simps(2) place_side.elims qualifyPlace_simps(4,5) x1.edge_from_open)
        apply clarsimp
        using that(1) toOpenOut_qualifyEdge apply simp
        apply clarsimp
          apply (metis (full_types) In_process_side_def Out_process_side_def Seq.prems(6) edge_in_flowI(2) fromOpenInI fromOpenIn_qualifyEdge
            process_side.exhaust x1.edge_from_open)
        apply (metis (full_types) In_process_side_def Out_process_side_def Seq.prems(3) edge_in_flowI(2) fromOpenInI x1x2.edge_from_open process_side.exhaust)
        apply (metis (full_types) In_process_side_def Out_process_side_def Seq.prems(3) edge_in_flowI(2) fromOpenInI x1x2.edge_from_open process_side.exhaust)
        done
    qed
    then consider
      e1' e2'
      where "e1' \<in> set (pg_edges (pgConstruct x1))" and "e2' \<in> set (pg_edges (pgConstruct x1))"
        and "edge_from e1' = p" and "edge_from e2' = p" and "e1' \<noteq> e2'"
    | e1' e2' p'
      where "e1' \<in> set (pg_edges (pgConstruct x2))" and "e2' \<in> set (pg_edges (pgConstruct x2))"
        and "edge_from e1' = p'" and "edge_from e2' = p'" and "e1' \<noteq> e2'"
        and "port.label (place_port p') = port.label (place_port p) \<or> (\<exists>x y. port.label (place_port p) = Repeatable x y)"
        and "p' \<in> set (pgraphPlaces (pgConstruct x2))" and "place_open p'"
    proof cases
      case 1
      then show ?thesis
        using that(1) Seq.prems(4,6,7,8)
        by (smt (verit, ccfv_SIG) image_iff qualifyEdge_simps(2) qualifyPlace_simps(2,4))
    next
      case 2
      then show ?thesis
      proof (cases "edge_to e1 = qualifyPlace SeqL (edge_to e2a)")
        case True
        then have False
          using 2 by (simp add: toOpenOut_def)
        then show ?thesis ..
      next
        case False
        then show ?thesis
          using 2 that(1)[of _ e2a] Seq.prems(4,6,8)
          by (smt (verit, ccfv_threshold) image_iff qualifyEdge_simps(2,3) qualifyPlace_simps(2,4))
      qed
    next
      case 3
      then show ?thesis
      proof (cases "edge_to e2 = qualifyPlace SeqL (edge_to e1a)")
        case True
        then have False
          using 3 by (simp add: toOpenOut_def)
        then show ?thesis ..
      next
        case False
        then show ?thesis
          using 3 that(1)[of e1a] Seq.prems(4,6,8)
          by (smt (verit, ccfv_threshold) image_iff qualifyEdge_simps(2,3) qualifyPlace_simps(2,4))
      qed
    next
      case 4
      then show ?thesis
      proof (cases "edge_to e1a = edge_to e2a")
        case True
        then have "edge_from e1b = edge_from e2b"
          using 4 by (metis place.inject(2) portSetSide_same)
        moreover have "e1b \<noteq> e2b"
          using 4(7,14) Seq.prems(4,6,7) by (metis edge.expand)
        moreover have
          " port.label (place_port (edge_from e1b)) = port.label (place_port p)
          \<or> (\<exists>x y. port.label (place_port p) = Repeatable x y)"
          using Seq.prems 4 pgConstruct_edge_carries_label
          by (metis Seq.hyps(2) True calculation(2) pgDefined.simps(4) place.disc(4) place_port.simps(2) portSetSide_label
              portSetSide_same qualifyPlace_simps(5) resource_neq(8,11) x2.edge_from_pg)
        moreover have "place_open (edge_from e1b)"
          using 4(4) by simp
        ultimately show ?thesis
          using 4 that(2)[of e1b e2b "edge_from e1b"] Seq.prems(4,6,7,8) x2.edge_from_pg by metis
      next
        case False
        then show ?thesis
          using 4 that(1)[of e1a e2a] Seq.prems(4,6,8)
          by (metis qualifyPlace_simps(2) qualifyPlace_simps(4))
      qed
    qed
    then show ?case
    proof cases
      case 1
      then show ?thesis
        using Seq.hyps(1) Seq.prems(1,8) x1.edge_from_pg
        by (metis pgDefined.simps(4))
    next
      case 2
      then show ?thesis
        using Seq.hyps(2) Seq.prems(1,8) x2.edge_from_pg
        by (metis pgDefined.simps(4))
    qed
  next
    case (Swap x1 x2a)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Par x1 x2)

    let ?shiftEdge =
      "shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))
                 (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"

    let ?shiftPortIn =
      "shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"

    have "port_graph_flow (pgConstruct (Par x1 x2))"
      using Par.prems(1,2) port_graph_flow_pgConstruct by blast
    then interpret x1x2: port_graph_flow "pgConstruct (Par x1 x2)" .
    have "port_graph_flow (pgConstruct x1)"
      using Par.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x1: port_graph_flow "pgConstruct x1" .
    have "port_graph_flow (pgConstruct x2)"
      using Par.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x2: port_graph_flow "pgConstruct x2" .

    have p_side: "port.side (place_port p) = In"
      using Par.prems(3,4,8) x1x2.edge_from_open place_side.elims
      by (metis (full_types) edge_in_flowI(2) in_out_distinct process_side.exhaust)
    then consider
      port where "p = OpenPort port" and "port \<in> set (pg_ports (pgConstruct x1))"
    | port where "p = OpenPort (?shiftPortIn port)" and "port \<in> set (pg_ports (pgConstruct x2))"
      using Par.prems(2,8) by (clarsimp) (elim disjE ; clarsimp)
    then consider
      port where "p = OpenPort port" and "port \<in> set (pg_ports (pgConstruct x1))"
             and "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
             and "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
    | port where "p = OpenPort (?shiftPortIn port)" and "port \<in> set (pg_ports (pgConstruct x2))"
             and "e1 \<in> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
             and "e2 \<in> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
    proof cases
      case 1
      moreover have "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e1 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "port.index (place_port (edge_from e1)) \<ge> length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using Par.prems(3,4,8) p_side by clarsimp
        moreover have "port.index (place_port (edge_from e1)) < length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using 1 Par.prems(4) p_side x1.ports_index_bound by (metis place_port.simps(2))
        ultimately show False
          by fastforce
      qed
      moreover have "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e2 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "port.index (place_port (edge_from e2)) \<ge> length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using Par.prems(5,6,8) p_side by clarsimp
        moreover have "port.index (place_port (edge_from e2)) < length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using 1 Par.prems(6) p_side x1.ports_index_bound by (metis place_port.simps(2))
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(1))
    next
      case 2
      moreover have "e1 \<in>  ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e1 \<notin> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "place_port (edge_from e1) \<in> set (pg_ports (pgConstruct x1))"
          using Par.prems(3,4,8) x1.edge_from_pg x1.open_port_pg by (clarsimp simp add: image_comp)
        then have "port.index (place_port (edge_from e1)) < length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using Par.prems(4) x1.ports_index_bound p_side by metis
        moreover have "port.index (place_port (edge_from e1)) \<ge> length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using 2 Par.prems(4) p_side by simp
        ultimately show False
          by fastforce
      qed
      moreover have
        "e2 \<in> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e2 \<notin> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "place_port (edge_from e2) \<in> set (pg_ports (pgConstruct x1))"
          using Par.prems(5,6,8) x1.edge_from_pg x1.open_port_pg by (clarsimp simp add: image_comp)
        then have "port.index (place_port (edge_from e2)) < length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using Par.prems(6) x1.ports_index_bound p_side by metis
        moreover have "port.index (place_port (edge_from e2)) \<ge> length (filter (\<lambda>x. port.side x = In) (pg_ports (pgConstruct x1)))"
          using 2 Par.prems(6) p_side by simp
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(2))
    qed
    then show ?case
    proof cases
      case 1
      then obtain e1' e2'
        where e1: "e1 = qualifyEdge ParL e1'" "e1' \<in> set (pg_edges (pgConstruct x1))"
          and e2: "e2 = qualifyEdge ParL e2'" "e2' \<in> set (pg_edges (pgConstruct x1))"
        by blast
      moreover have "p \<in> set (pgraphPlaces (pgConstruct x1))"
        using 1(1,2) by simp
      moreover have "edge_from e1' = p"
        using Par.prems(4,8) e1(1) by fastforce
      moreover have "edge_from e2' = p"
        using Par.prems(6,8) e2(1) by force
      moreover have "e1' \<noteq> e2'"
        using e1 e2 Par.prems(7) by blast
      ultimately show ?thesis
        using Par.prems(1,2)
        using Par.hyps(1)[of p e1' e2']
        by (metis Par.prems(8) pgDefined.simps(5))
    next
      case 2
      then obtain e1' e2'
        where e1: "e1 = ?shiftEdge (qualifyEdge ParR e1')" "e1' \<in> set (pg_edges (pgConstruct x2))"
          and e2: "e2 = ?shiftEdge (qualifyEdge ParR e2')" "e2' \<in> set (pg_edges (pgConstruct x2))"
        by blast
      moreover have "OpenPort port \<in> set (pgraphPlaces (pgConstruct x2))"
        using 2(2) by simp
      moreover have "edge_from e1' = OpenPort port"
        using Par.prems(4)[symmetric] Par.prems(8) e1(1) 2(1) apply (cases "edge_from e1'" ; simp)
        using inj_shiftPort[THEN inj_onD] by blast
      moreover have "edge_from e2' = OpenPort port"
        using Par.prems(6)[symmetric] Par.prems(8) e2(1) 2(1) apply (cases "edge_from e2'" ; simp)
        using inj_shiftPort[THEN inj_onD] by blast
      moreover have "e1' \<noteq> e2'"
        using e1 e2 Par.prems(7) by blast
      moreover have "port.label (place_port (OpenPort port)) = port.label (place_port p)"
        using 2(1) by simp
      ultimately show ?thesis
        using Par.prems(1,2)
        using Par.hyps(2)[of "OpenPort port" e1' e2']
        by (simp add: place.discI(2))
    qed
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
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip del: disjCI ; blast)
      done
  next
    case (Erase x)
    then show ?case by simp
  next
    case (Represent x)
    then show ?case by simp
  next
    case (Apply x1 x2a)
    then show ?case by simp
  next
    case (Repeat x1 x2a)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip del: disjCI ; blast)
      done
  next
    case (Close x1 x2a)
    then show ?case by simp
  next
    case (Once x1 x2a)
    then show ?case by simp
  next
    case (Forget x)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  qed
qed

text\<open>Any ground port with two distinct edges touching it (and thus more than one destination) must carry a copyable resource\<close>
lemma pgConstruct_edge_copy_ground:
  assumes "pgDefined x"
      and "p \<in> set (pgraphPlaces (pgConstruct x))"
      and "e1 \<in> set (pg_edges (pgConstruct x))"
      and "edge_from e1 = p"
      and "e2 \<in> set (pg_edges (pgConstruct x))"
      and "edge_from e2 = p"
      and "e1 \<noteq> e2"
      and "place_ground p"
    shows "(\<exists>a. port.label (place_port p) = Copyable a) \<or> (\<exists>a b. port.label (place_port p) = Repeatable a b)"
proof -
  show ?thesis
    using assms
  proof (induct x arbitrary: p e1 e2)
    case (Primitive x1 x2a x3 x4)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  next
    case (Identity x)
    have False
      using Identity(2,8) by fastforce
    then show ?case by simp
  next
    case (Seq x1 x2)

    have pg: "pgConstruct (Seq x1 x2) = seqPortGraphs (qualifyPortGraph SeqL (pgConstruct x1)) (qualifyPortGraph SeqR (pgConstruct x2))"
      (is "_ = seqPortGraphs ?pg1 ?pg2")
      by simp
    let ?pg = "seqPortGraphs ?pg1 ?pg2"

    have pgf1': "port_graph_flow ?pg1"
      using Seq by (metis pgDefined.simps(4) port_graph_flow_pgConstruct port_graph_flow_qualifyPortGraph)
    have pgf1: "port_graph_flow (pgConstruct x1)"
      using Seq.prems(1) pgDefined.simps(4) port_graph_flow_pgConstruct by blast
    have pgf2': "port_graph_flow ?pg2"
      using Seq by (metis pgDefined.simps(4) port_graph_flow_pgConstruct port_graph_flow_qualifyPortGraph)
    have pgf2: "port_graph_flow (pgConstruct x2)"
      using Seq.prems(1) pgDefined.simps(4) port_graph_flow_pgConstruct by blast

    consider
      n where "n \<in> qualifyNode SeqL ` set (pg_nodes (pgConstruct x1))" and "p \<in> set (nodePlaces n)"
    | n where "n \<in> qualifyNode SeqR ` set (pg_nodes (pgConstruct x2))" and "p \<in> set (nodePlaces n)"
      using Seq.prems(2,8) pgraphPlaces_ground in_nodes_seqPortGraphsE
      by (metis (no_types, lifting) list.set_map pg qualifyPortGraph_simps(2))
    then consider
      n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqL p'"
    | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqR p'"
      by (cases ; metis (no_types, opaque_lifting) imageE list.set_map qualifyNode_places)
    then consider
      n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqL p'"
             and " e1 \<notin> set (seqInterfaceEdges (qualifyPortGraph SeqL (pgConstruct x1)) (qualifyPortGraph SeqR (pgConstruct x2)))
                 \<or> e2 \<notin> set (seqInterfaceEdges (qualifyPortGraph SeqL (pgConstruct x1)) (qualifyPortGraph SeqR (pgConstruct x2)))"
    | n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqL p'"
             and "e1 \<in> set (seqInterfaceEdges (qualifyPortGraph SeqL (pgConstruct x1)) (qualifyPortGraph SeqR (pgConstruct x2)))"
             and "e2 \<in> set (seqInterfaceEdges (qualifyPortGraph SeqL (pgConstruct x1)) (qualifyPortGraph SeqR (pgConstruct x2)))"
    | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqR p'"
      by metis
    then show ?case
    proof cases
      case 1
      \<comment> \<open>If @{term p'} is in port graph of @{term x1} then edges starting from it must be either
          fully in the port graph of @{term x1} or in the stitch.
          If one is in the stitch then we are interested in the left part of that stitch which is
          fully in the port graph of @{term x1}.
          If both are in the stitch then we might need to inspect the right part, which will be
          the next case.\<close>
      (* If they are both in the stitch then it is up to whether left parts have equal destinations.
         If they don't then we can use left parts for induction.
         If they do then we have to use right parts for induction.
         If they are not both in the stitch then all we need are the left parts.
       *)

      have p'_places: "p' \<in> set (pgraphPlaces (pgConstruct x1))"
        using 1(1,2) by simp blast
      moreover obtain e1' e2'
        where e1': "e1' \<in> set (pg_edges (pgConstruct x1))" "edge_from e1' = p'"
          and e2': "e2' \<in> set (pg_edges (pgConstruct x1))" "edge_from e2' = p'"
          and "e1' \<noteq> e2'"
        using pgf1' pgf2' Seq(5)[unfolded pg]
      proof (cases rule: seqPortGraphs_edge_cases)
        case e1: Stitch
        show ?thesis
          using pgf1' pgf2' Seq(7)[unfolded pg]
        proof (cases rule: seqPortGraphs_edge_cases)
          case Stitch
          then show ?thesis using e1 1(4) by blast
        next
          case L
          then show ?thesis
            using e1 that
            apply (elim seqInterfaceEdges_setD)
            by clarsimp
               (metis "1"(3) Seq.prems(4,6) pgf1 place.disc(4) port_graph_flow.edge_to_open qualifyEdge_simps(2)
              qualifyPlace_simps(4) toOpenOutI unqualify_qualify_place_inv)
        next
          case R
          then show ?thesis
            by clarsimp
               (metis R(1) Seq.prems(4,6,8) e1 pgf1' pgf2' place.distinct_disc(1) place_in_pg_disjoint
                port_graph.edge_from_pg port_graph_flow.axioms(1) process_inner.distinct(1) qualifyPortGraph_apart seqInterfaceEdges_setD)
        qed
      next
        case e1: L
        show ?thesis
          using pgf1' pgf2' Seq(7)[unfolded pg]
        proof (cases rule: seqPortGraphs_edge_cases)
          case Stitch
          then show ?thesis
            using e1 that
            apply (elim seqInterfaceEdges_setD)
            by clarsimp
               (metis "1"(3) Seq.prems(4,6) pgf1 place.disc(4) port_graph_flow.edge_to_open qualifyEdge_simps(2)
                 qualifyPlace_simps(4) toOpenOutI unqualify_qualify_place_inv)
        next
          case L
          then show ?thesis
            using e1 that
            by clarsimp
               (metis "1"(3) Seq.prems(4,6,7) qualifyEdge_simps(2) unqualify_qualify_place_inv)
        next
          case R
          then show ?thesis
            by clarsimp
               (metis "1"(3) Seq.prems(6,8) list.inject process_inner.distinct(1) qualifyEdge_simps(2) qualifyPlace_simps(1,3))
        qed
      next
        case R
        then show ?thesis
          by clarsimp
             (metis "1"(3) Seq.prems(4,8) list.inject process_inner.distinct(1) qualifyEdge_simps(2)
                qualifyPlace_simps(1) qualifyPlace_simps(3))
      qed
      ultimately show ?thesis
        using Seq.hyps(1)[of p' e1' e2']
        by (metis "1"(3) Seq.prems(1,8) pgDefined.simps(4) qualifyPlace_simps(3,5))
    next
      case 2
      \<comment> \<open>If @{term p'} is in port graph of @{term x1} and both edges are in the stitch then we
          need to ask whether the destinations of their left parts are the same.
          If they are different then we are interested in those left parts of the stitch.
          If they are equal then we are interested in the right parts of the stitch which now
          originate from open places and thus the other theorem @{thm pgConstruct_edge_copy_open} applies.\<close>

      obtain e1a e1b e2a e2b and port2 port1 :: "(process_side, ('a, 'b) resource) port"
        where "e1a \<in> set (pg_edges (pgConstruct x1))" and "e1b \<in> set (pg_edges (pgConstruct x2))"
          and "edge_to e1a = OpenPort (portSetSide Out port1)" and "edge_from e1b = OpenPort (portSetSide In port1)"
          and "port.side port1 = Out"
          and "edge_from e1 = qualifyPlace SeqL (edge_from e1a)" and "edge_to e1 = qualifyPlace SeqR (edge_to e1b)"
          and "e2a \<in> set (pg_edges (pgConstruct x1))" and "e2b \<in> set (pg_edges (pgConstruct x2))"
          and "edge_to e2a = OpenPort (portSetSide Out port2)" and "edge_from e2b = OpenPort (portSetSide In port2)"
          and "port.side port2 = Out"
          and "edge_from e2 = qualifyPlace SeqL (edge_from e2a)" and "edge_to e2 = qualifyPlace SeqR (edge_to e2b)"
        using 2(4,5)
        apply (elim seqInterfaceEdges_setD)
        by clarsimp (metis place.disc(4) qualifyPlace_simps(2) qualifyPlace_simps(4))
      note es = this

      show ?thesis
      proof (cases "edge_to e1a = edge_to e2a")
        case True
        \<comment> \<open>Equal destinations, so use right parts\<close>
        then have "edge_from e1b = edge_from e2b"
          using es by (metis place.inject(2) portSetSide_same)
        then show ?thesis
          using pgConstruct_edge_copy_open[of _ "edge_from e1b" e1b e2b] es Seq.prems(1,4,6,7) True pgConstruct_edge_carries_label
          by (metis edge.expand pgDefined.simps(4) pgf2 place.discI(2) place_port.simps(2) portSetSide_label port_graph.edge_from_pg
              port_graph_flow.axioms(1) qualifyPlace_simps(5) resource_neq(8,11))
      next
        case False
        \<comment> \<open>Distinct destinations, so use left parts\<close>
        then show ?thesis
          using Seq.hyps(1)[of p' e1a e2a] es 2(3) Seq.prems(1,4,6,8)
          by (metis pgDefined.simps(4) pgf1 port_graph.edge_from_pg port_graph_flow.axioms(1)
              qualifyPlace_simps(3,5) unqualify_qualify_place_inv)
      qed
    next
      case 3
      \<comment> \<open>If @{term p'} is in port graph of @{term x2} then edges starting from it must be fully in
          the port graph of @{term x2}.\<close>

      have p'_places: "p' \<in> set (pgraphPlaces (pgConstruct x2))"
        using 3(1,2) by simp blast
      moreover obtain e1'
        where e1': "e1' \<in> set (pg_edges (pgConstruct x2))" "edge_from e1' = p'" "edge_to e1 = qualifyPlace SeqR (edge_to e1')"
        using pgf1' pgf2' Seq(5)[unfolded pg]
      proof (cases rule: seqPortGraphs_edge_cases)
        case Stitch
        then have "hd (place_name (edge_from e1)) = SeqL"
          using Seq.prems(4,8) by (clarsimp elim!: seqInterfaceEdges_setD simp del: seqInterfaceEdges.simps)
        moreover have "hd (place_name (edge_from e1)) = SeqR"
          using 3(3) p'_places Seq.prems(4,8) by clarsimp
        ultimately show ?thesis
          by simp
      next
        case L
        then have "hd (place_name (edge_from e1)) = SeqL"
          using Seq.prems(4,8) by clarsimp
        moreover have "hd (place_name (edge_from e1)) = SeqR"
          using 3(3) p'_places Seq.prems(4,8) by clarsimp
        ultimately show ?thesis
          by simp
      next
        case R
        then show ?thesis
          using Seq.prems(4) 3(3)
          apply clarsimp
          apply (drule injD[OF inj_qualifyPlace])
          by (rule that) simp_all
      qed
      moreover obtain e2'
        where e2': "e2' \<in> set (pg_edges (pgConstruct x2))" "edge_from e2' = p'" "edge_to e2 = qualifyPlace SeqR (edge_to e2')"
        using pgf1' pgf2' Seq(7)[unfolded pg]
      proof (cases rule: seqPortGraphs_edge_cases)
        case Stitch
        then have "hd (place_name (edge_from e2)) = SeqL"
          using Seq.prems(6,8) by (clarsimp elim!: seqInterfaceEdges_setD simp del: seqInterfaceEdges.simps)
        moreover have "hd (place_name (edge_from e2)) = SeqR"
          using 3(3) p'_places Seq.prems(6,8) by clarsimp
        ultimately show ?thesis
          by simp
      next
        case L
        then have "hd (place_name (edge_from e2)) = SeqL"
          using Seq.prems(6,8) by clarsimp
        moreover have "hd (place_name (edge_from e2)) = SeqR"
          using 3(3) p'_places Seq.prems(6,8) by clarsimp
        ultimately show ?thesis
          by simp
      next
        case R
        then show ?thesis
          using Seq.prems(6) 3(3)
          apply clarsimp
          apply (drule injD[OF inj_qualifyPlace])
          by (rule that) simp_all
      qed
      moreover have "e1' \<noteq> e2'"
        using e1'(3) e2'(3) Seq.prems(4,6,7) by (metis edge.expand)
      ultimately show ?thesis
        using Seq.hyps(2)[of p' e1' e2']
        by (metis 3(3) Seq.prems(1,8) pgDefined.simps(4) qualifyPlace_simps(3,5))
    qed
  next
    case (Swap x1 x2a)
    have False
      using Swap(2,8) by fastforce
    then show ?case by simp
  next
    case (Par x1 x2)

    let ?shift =
      "shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))
                 (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"

    consider
      n where "n \<in> qualifyNode ParL ` set (pg_nodes (pgConstruct x1))" and "p \<in> set (nodePlaces n)"
    | n where "n \<in> qualifyNode ParR ` set (pg_nodes (pgConstruct x2))" and "p \<in> set (nodePlaces n)"
      using Par.prems(2,8) pgraphPlaces_ground in_nodes_juxtaposeE
      by (metis (no_types, lifting) list.set_map pgConstruct.simps(3) qualifyPortGraph_simps(2))
    then consider
      n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParL p'"
    | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParR p'"
      by (cases ; metis (no_types, opaque_lifting) imageE list.set_map qualifyNode_places)
    then consider
      n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParL p'"
             and "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
             and "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
    | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParR p'"
             and "e1 \<in> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
             and "e2 \<in> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
    proof cases
      case 1
      moreover have "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e1 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "hd (place_name (edge_from e1)) = ParR"
          using Par.prems(3,4,8) by clarsimp
        moreover have "hd (place_name (edge_from e1)) = ParL"
          using 1 Par.prems(4) by clarsimp
        ultimately show False
          by fastforce
      qed
      moreover have "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e2 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "hd (place_name (edge_from e2)) = ParR"
          using Par.prems(5,6,8) by clarsimp
        moreover have "hd (place_name (edge_from e2)) = ParL"
          using 1 Par.prems(6) by clarsimp
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(1))
    next
      case 2
      moreover have "e1 \<in>  ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e1 \<notin> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "hd (place_name (edge_from e1)) = ParL"
          using Par.prems(3,4,8) by (clarsimp simp add: image_comp)
        moreover have "hd (place_name (edge_from e1)) = ParR"
          using 2 Par.prems(4) by clarsimp
        ultimately show False
          by fastforce
      qed
      moreover have
        "e2 \<in> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e2 \<notin> shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))
           (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1)))) `
          qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "hd (place_name (edge_from e2)) = ParL"
          using Par.prems(5,6,8) by (clarsimp simp add: image_comp)
        moreover have "hd (place_name (edge_from e2)) = ParR"
          using 2 Par.prems(6) by clarsimp
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(2))
    qed
    then show ?case
    proof cases
      case 1
      then obtain e1' e2'
        where e1: "e1 = qualifyEdge ParL e1'" "e1' \<in> set (pg_edges (pgConstruct x1))"
          and e2: "e2 = qualifyEdge ParL e2'" "e2' \<in> set (pg_edges (pgConstruct x1))"
        by blast
      moreover have "p' \<in> set (pgraphPlaces (pgConstruct x1))"
        using 1(1,2) by simp blast
      moreover have "edge_from e1' = p'"
        by (metis "1"(3) Par.prems(4) e1(1) qualifyEdge_simps(2) unqualify_qualify_place_inv)
      moreover have "edge_from e2' = p'"
        by (metis "1"(3) Par.prems(6) e2(1) qualifyEdge_simps(2) unqualify_qualify_place_inv)
      moreover have "e1' \<noteq> e2'"
        using e1 e2 Par.prems(7) by blast
      moreover have "port.label (place_port p') = port.label (place_port p)"
        using 1(3) by simp
      ultimately show ?thesis
        using Par.prems(1,2)
        using Par.hyps(1)[of p' e1' e2']
        by (metis "1"(3) Par.prems(8) pgDefined.simps(5) qualifyPlace_simps(3))
    next
      case 2
      then obtain e1' e2'
        where e1: "e1 = ?shift (qualifyEdge ParR e1')" "e1' \<in> set (pg_edges (pgConstruct x2))"
          and e2: "e2 = ?shift (qualifyEdge ParR e2')" "e2' \<in> set (pg_edges (pgConstruct x2))"
        by blast
      moreover have "p' \<in> set (pgraphPlaces (pgConstruct x2))"
        using 2(1,2) by simp blast
      moreover have "edge_from e1' = p'"
        by (metis "2"(3) Par.prems(4,8) e1(1) qualifyEdge_simps(2) shiftOpenInEdge_simps(1) shiftOpenPlace_ground(1,2) unqualify_qualify_place_inv)
      moreover have "edge_from e2' = p'"
        by (metis "2"(3) Par.prems(6,8) e2(1) qualifyEdge_simps(2) shiftOpenInEdge_simps(1) shiftOpenPlace_ground(1,2) unqualify_qualify_place_inv)
      moreover have "e1' \<noteq> e2'"
        using e1 e2 Par.prems(7) by blast
      moreover have "port.label (place_port p') = port.label (place_port p)"
        using 2(3) by simp
      ultimately show ?thesis
        using Par.prems(1,2)
        using Par.hyps(2)[of p' e1' e2']
        by (metis "2"(3) Par.prems(8) pgDefined.simps(5) qualifyPlace_simps(3))
    qed
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
    have False
      using Duplicate(2,8) by fastforce
    then show ?case by simp
  next
    case (Erase x)
    have False
      using Erase(2,8) by fastforce
    then show ?case by simp
  next
    case (Represent x)
    then show ?case by simp
  next
    case (Apply x1 x2a)
    then show ?case by simp
  next
    case (Repeat x1 x2a)
    have False
      using Repeat(2,8) by fastforce
    then show ?case by simp
  next
    case (Close x1 x2a)
    have False
      using Close(2,8) by fastforce
    then show ?case by simp
  next
    case (Once x1 x2a)
    then show ?case by fastforce
  next
    case (Forget x)
    then show ?case
      apply (simp del: parallelPorts.simps)
      apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
      done
  qed
qed

text\<open>For any place not labelled with the anything resource, if there are two edges coming into it then they are equal\<close>
lemma pgConstruct_edge_noMerge_open:
  assumes "pgDefined x"
      and "p \<in> set (pgraphPlaces (pgConstruct x))"
      and "e1 \<in> set (pg_edges (pgConstruct x))"
      and "edge_to e1 = p"
      and "e2 \<in> set (pg_edges (pgConstruct x))"
      and "edge_to e2 = p"
      and "place_open p"
      and "port.label (place_port p) \<noteq> Anything"
    shows "e1 = e2"
  using assms
proof (induct x arbitrary: p e1 e2)
  case (Primitive x1 x2a x3 x4)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Identity x)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Seq x1 x2)

  have "port_graph_flow (pgConstruct (Seq x1 x2))"
    using Seq.prems(1,2) port_graph_flow_pgConstruct by blast
  then interpret x1x2: port_graph_flow "pgConstruct (Seq x1 x2)" .
  have pgf1: "port_graph_flow (pgConstruct x1)"
    using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
  then interpret x1: port_graph_flow "pgConstruct x1" .
  have pgf2: "port_graph_flow (pgConstruct x2)"
    using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
  then interpret x2: port_graph_flow "pgConstruct x2" .

  consider
    \<comment> \<open>The edges are either both in the right side or both in stitch.
        They cannot be in the left side because they both go to an open output of the composition.
        They cannot be mixed stitch and right side because the right side of the stitch would go to
        the same place as the fully right edge, so by hypothesis would be the same but one goes from
        an open place and the other from a ground place. \<close>
        "e1 \<in> qualifyEdge SeqR ` set (pg_edges (pgConstruct x2))" and "\<not> fromOpenIn e1"
    and "e2 \<in> qualifyEdge SeqR ` set (pg_edges (pgConstruct x2))" and "\<not> fromOpenIn e2"
    | e1a e1b e2a e2b and port1 port2 :: "(process_side, ('a, 'b) resource) port"
    where "e1a \<in> set (pg_edges (pgConstruct x1))" and "e1b \<in> set (pg_edges (pgConstruct x2))"
      and "edge_to e1a = OpenPort (portSetSide Out port1)" and "edge_from e1b = OpenPort (portSetSide In port1)"
      and "port.side port1 = Out"
      and "edge_from e1 = qualifyPlace SeqL (edge_from e1a)" and "edge_to e1 = qualifyPlace SeqR (edge_to e1b)"
      and "e2a \<in> set (pg_edges (pgConstruct x1))" and "e2b \<in> set (pg_edges (pgConstruct x2))"
      and "edge_to e2a = OpenPort (portSetSide Out port2)" and "edge_from e2b = OpenPort (portSetSide In port2)"
      and "port.side port2 = Out"
      and "edge_from e2 = qualifyPlace SeqL (edge_from e2a)" and "edge_to e2 = qualifyPlace SeqR (edge_to e2b)"
  proof -
    show ?thesis
      \<comment> \<open>This really just gets all nine cases and massages each into the right form or shows it's a contradiction\<close>
      using Seq.prems(3-8)
      apply (simp del: seqPortGraphs.simps)
      apply (subst (asm) (1 2) seqPortGraphs_flow_edges[OF port_graph_flow_qualifyPortGraph[OF pgf1] port_graph_flow_qualifyPortGraph[OF pgf2]])
      apply (clarsimp simp del: seqInterfaceEdges.simps)
      apply (elim disjE seqInterfaceEdges_setD conjE)
      apply clarsimp
      using that(2) apply (metis place.disc(4) portSetSide_same qualifyPlace_simps(2,4))
      apply clarsimp
             apply (metis Seq.prems(6) toOpenOutI toOpenOut_qualifyEdge x2.edge_to_open)
            apply clarsimp
            apply (metis Seq.hyps(2) Seq.prems(1) fromOpenInI pgDefined.simps(4)
          place.disc(4) qualifyPlace_simps(2) qualifyPlace_simps(4) x2.edge_from_open x2.edge_to_pg)
      apply (metis pgf2 port_graph_flow.edge_to_open port_graph_flow_qualifyPortGraph toOpenOutI)
            apply clarsimp
          apply (metis Seq.hyps(2) Seq.prems(1) fromOpenInI pgDefined.simps(4)
          place.disc(4) qualifyPlace_simps(2) qualifyPlace_simps(4) x2.edge_from_open x2.edge_to_pg)
      apply (metis (full_types) In_process_side_def Out_process_side_def Seq.prems(5) edge_in_flowI(3) process_side.exhaust toOpenOutI x1x2.edge_to_open)
      apply (metis (full_types) In_process_side_def Out_process_side_def Seq.prems(5) edge_in_flowI(3) process_side.exhaust toOpenOutI x1x2.edge_to_open)
      apply (metis (full_types) In_process_side_def Out_process_side_def Seq.prems(5) edge_in_flowI(3) process_side.exhaust toOpenOutI x1x2.edge_to_open)
      using that(1) apply blast
      done
  qed
  then show ?case
  proof cases
    case 1
    then show ?thesis
      apply clarsimp
      using Seq.hyps(2) Seq.prems(1,4,6,7,8)
      by (metis (no_types, lifting) pgDefined.simps(4) qualifyEdge_simps(3) qualifyPlace_simps(2,4) x2.edge_to_pg)
  next
    case 2
    then show ?thesis
      apply clarsimp
      using Seq.hyps(1,2) Seq.prems(1,4,6,7,8)
      by (metis edge.collapse pgDefined.simps(4) pgConstruct_edge_carries_label place.disc(4) place_port.simps(2) port.collapse
          portSetSide_index portSetSide_label qualifyPlace_simps(2) qualifyPlace_simps(4) resource_neq(11) x1.edge_to_pg x2.edge_to_pg)
  qed
next
  case (Swap x1 x2a)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Par x1 x2)

    let ?shiftEdge =
      "shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))
                 (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"

    let ?shiftPortOut =
      "shiftPort (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"

    have "port_graph_flow (pgConstruct (Par x1 x2))"
      using Par.prems(1,2) port_graph_flow_pgConstruct by blast
    then interpret x1x2: port_graph_flow "pgConstruct (Par x1 x2)" .
    have "port_graph_flow (pgConstruct x1)"
      using Par.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x1: port_graph_flow "pgConstruct x1" .
    have "port_graph_flow (pgConstruct x2)"
      using Par.prems(1,2) port_graph_flow_pgConstruct by auto
    then interpret x2: port_graph_flow "pgConstruct x2" .

    have p_side: "port.side (place_port p) = Out"
      using Par.prems(3,4,7) x1x2.edge_to_open place_side.elims
      by (metis (full_types) edge_in_flowI(3) in_out_distinct process_side.exhaust)
    then consider
      port where "p = OpenPort port" and "port \<in> set (pg_ports (pgConstruct x1))"
    | port where "p = OpenPort (?shiftPortOut port)" and "port \<in> set (pg_ports (pgConstruct x2))"
      using Par.prems(2,7) by (clarsimp) (elim disjE ; clarsimp)
    then consider
      port where "p = OpenPort port" and "port \<in> set (pg_ports (pgConstruct x1))"
             and "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
             and "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
    | port where "p = OpenPort (?shiftPortOut port)" and "port \<in> set (pg_ports (pgConstruct x2))"
             and "e1 \<in> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
             and "e2 \<in> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
    proof cases
      case 1
      moreover have "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e1 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "port.index (place_port (edge_to e1)) \<ge> length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using Par.prems(3,4,7) p_side by clarsimp
        moreover have "port.index (place_port (edge_to e1)) < length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using 1 Par.prems(4) p_side x1.ports_index_bound by (metis place_port.simps(2))
        ultimately show False
          by fastforce
      qed
      moreover have "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e2 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "port.index (place_port (edge_to e2)) \<ge> length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using Par.prems(5,6,7) p_side by clarsimp
        moreover have "port.index (place_port (edge_to e2)) < length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using 1 Par.prems(6) p_side x1.ports_index_bound by (metis place_port.simps(2))
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(1))
    next
      case 2
      moreover have "e1 \<in>  ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e1 \<notin> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "place_port (edge_to e1) \<in> set (pg_ports (pgConstruct x1))"
          using Par.prems(3,4,7) x1.edge_to_pg x1.open_port_pg by (clarsimp simp add: image_comp)
        then have "port.index (place_port (edge_to e1)) < length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using Par.prems(4) x1.ports_index_bound p_side by metis
        moreover have "port.index (place_port (edge_to e1)) \<ge> length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using 2 Par.prems(4) p_side by simp
        ultimately show False
          by fastforce
      qed
      moreover have
        "e2 \<in> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e2 \<notin> ?shiftEdge ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "place_port (edge_to e2) \<in> set (pg_ports (pgConstruct x1))"
          using Par.prems(5,6,7) x1.edge_to_pg x1.open_port_pg by (clarsimp simp add: image_comp)
        then have "port.index (place_port (edge_to e2)) < length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using Par.prems(6) x1.ports_index_bound p_side by metis
        moreover have "port.index (place_port (edge_to e2)) \<ge> length (filter (\<lambda>x. port.side x = Out) (pg_ports (pgConstruct x1)))"
          using 2 Par.prems(6) p_side by simp
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(2))
    qed
    then show ?case
    proof cases
      case 1
      then show ?thesis
        apply clarsimp
        using Par.hyps(1) Par.prems(1,4,6,7,8)
        by (metis pgDefined.simps(5) qualifyEdge_simps(3) qualifyPlace_simps(2,4) x1.edge_to_pg)
    next
      case 2
      then show ?thesis
        apply clarsimp
        apply (subgoal_tac "xb = xc")
        apply blast
        apply (rule_tac p = "edge_to xb" in Par.hyps(2))
        using Par.prems(1) apply simp
        using x2.edge_to_pg apply presburger
            apply assumption
           apply (rule refl)
          apply assumption
        using Par.prems(4,6,7,8) apply clarsimp
          apply (metis (no_types, lifting) add_diff_cancel_left' place_open_def place_port.simps(2) port.collapse qualifyPlace_simps(2,4)
            shiftOpenPlace_open shiftPort_simps(2,3,4))
        apply (metis Par.prems(4,7) p_side place_side.simps shiftOpenInEdge_toOpenOut toOpenOut_def toOpenOut_qualifyEdge)
        by (metis Par.prems(4,8) qualifyEdge_simps(3) qualifyPlace_simps(5) shiftOpenInEdge_simps(2) shiftOpenPlace_label)
    qed
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
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Erase x)
  then show ?case by simp
next
  case (Represent x)
  then show ?case by simp
next
  case (Apply x1 x2a)
  then show ?case by simp
next
  case (Repeat x1 x2a)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Close x1 x2a)
  then show ?case by simp
next
  case (Once x1 x2a)
  then show ?case by simp
next
  case (Forget x)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
qed

lemma pgConstruct_edge_noMerge_ground:
  assumes "pgDefined x"
      and "p \<in> set (pgraphPlaces (pgConstruct x))"
      and "e1 \<in> set (pg_edges (pgConstruct x))"
      and "edge_to e1 = p"
      and "e2 \<in> set (pg_edges (pgConstruct x))"
      and "edge_to e2 = p"
      and "place_ground p"
      and "port.label (place_port p) \<noteq> Anything"
    shows "e1 = e2"
  using assms
proof (induct x arbitrary: p e1 e2)
  case (Primitive x1 x2a x3 x4)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Identity x)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Seq x1 x2)

  have "port_graph_flow (pgConstruct (Seq x1 x2))"
    using Seq.prems(1,2) port_graph_flow_pgConstruct by blast
  then interpret x1x2: port_graph_flow "pgConstruct (Seq x1 x2)" .
  have pgf1: "port_graph_flow (pgConstruct x1)"
    using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
  then interpret x1: port_graph_flow "pgConstruct x1" .
  have pgf2: "port_graph_flow (pgConstruct x2)"
    using Seq.prems(1,2) port_graph_flow_pgConstruct by auto
  then interpret x2: port_graph_flow "pgConstruct x2" .

  consider
    n where "n \<in> qualifyNode SeqL ` set (pg_nodes (pgConstruct x1))" and "p \<in> set (nodePlaces n)"
  | n where "n \<in> qualifyNode SeqR ` set (pg_nodes (pgConstruct x2))" and "p \<in> set (nodePlaces n)"
    using Seq.prems(2,7) pgraphPlaces_ground in_nodes_seqPortGraphsE
    by (metis (mono_tags, lifting) list.set_map pgConstruct.simps(2) qualifyPortGraph_simps(2))
  then consider
    n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqL p'"
  | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqR p'"
    by (cases ; metis (no_types, opaque_lifting) imageE list.set_map qualifyNode_places)
  then consider
    n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqL p'"
           and "e1 \<in> qualifyEdge SeqL ` set (pg_edges (pgConstruct x1))"
           and "e2 \<in> qualifyEdge SeqL ` set (pg_edges (pgConstruct x1))"
  | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqR p'"
           and "e1 \<in> qualifyEdge SeqR ` set (pg_edges (pgConstruct x2))" and "\<not> fromOpenIn e1"
           and "e2 \<in> qualifyEdge SeqR ` set (pg_edges (pgConstruct x2))" and "\<not> fromOpenIn e2"
  | n p' e1a e1b e2a e2b and port1 port2 :: "(process_side, ('a, 'b) resource) port"
         where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace SeqR p'"
           and "e1a \<in> set (pg_edges (pgConstruct x1))" and "e1b \<in> set (pg_edges (pgConstruct x2))"
           and "edge_to e1a = OpenPort (portSetSide Out port1)" and "edge_from e1b = OpenPort (portSetSide In port1)"
           and "port.side port1 = Out"
           and "edge_from e1 = qualifyPlace SeqL (edge_from e1a)" and "edge_to e1 = qualifyPlace SeqR (edge_to e1b)"
           and "e2a \<in> set (pg_edges (pgConstruct x1))" and "e2b \<in> set (pg_edges (pgConstruct x2))"
           and "edge_to e2a = OpenPort (portSetSide Out port2)" and "edge_from e2b = OpenPort (portSetSide In port2)"
           and "port.side port2 = Out"
           and "edge_from e2 = qualifyPlace SeqL (edge_from e2a)" and "edge_to e2 = qualifyPlace SeqR (edge_to e2b)"
  proof cases
    case 1
    then show ?thesis
      apply (rule that(1))
      using Seq.prems(3,4,7)
      apply (simp del: seqPortGraphs.simps)
       apply (subst (asm) seqPortGraphs_flow_edges[OF port_graph_flow_qualifyPortGraph[OF pgf1] port_graph_flow_qualifyPortGraph[OF pgf2]])
      apply (clarsimp simp del: seqInterfaceEdges.simps)
      apply (elim disjE seqInterfaceEdges_setD conjE)
      apply clarsimp
         apply (metis "1"(3) list.inject process_inner.distinct(1) qualifyPlace_simps(1) unqualify_qualify_place_inv)
      apply assumption
      apply clarsimp
      apply (metis "1"(3) list.sel(1) process_inner.distinct(1) qualifyPlace_simps(1) unqualify_qualify_place_inv)
      using Seq.prems(5,6,7)
      apply (simp del: seqPortGraphs.simps)
       apply (subst (asm) seqPortGraphs_flow_edges[OF port_graph_flow_qualifyPortGraph[OF pgf1] port_graph_flow_qualifyPortGraph[OF pgf2]])
      apply (clarsimp simp del: seqInterfaceEdges.simps)
      apply (elim disjE seqInterfaceEdges_setD conjE)
      apply clarsimp
         apply (metis "1"(3) list.inject process_inner.distinct(1) qualifyPlace_simps(1) unqualify_qualify_place_inv)
      apply assumption
      apply clarsimp
      apply (metis "1"(3) list.sel(1) process_inner.distinct(1) qualifyPlace_simps(1) unqualify_qualify_place_inv)
      done
  next
    case 2
    then show ?thesis
      \<comment> \<open>This really just gets all nine cases and massages each into the right form or shows it's a contradiction\<close>
      using Seq.prems(3,4,5,6,7,8)
      apply (simp del: seqPortGraphs.simps)
      apply (subst (asm) (1 2) seqPortGraphs_flow_edges[OF port_graph_flow_qualifyPortGraph[OF pgf1] port_graph_flow_qualifyPortGraph[OF pgf2]])
      apply (clarsimp simp del: seqInterfaceEdges.simps)
      apply (elim disjE seqInterfaceEdges_setD conjE)
      apply clarsimp
      using that(3)
      apply (smt (z3) "2"(2,3) place.discI(2) portSetSide_same qualifyPlace_simps(2) qualifyPlace_simps(4))
      apply clarsimp
      apply (metis Seq.prems(7) list.sel(1) process_inner.distinct(1) qualifyPlace_simps(1) qualifyPlace_simps(3))
      apply clarsimp
            apply (metis Seq.hyps(2) Seq.prems(1,7,8) fromOpenIn_def pgDefined.simps(4)
          place.disc(4) qualifyPlace_simps(3,4,5) unqualify_qualify_place_inv x2.edge_from_open x2.edge_to_pg)
      apply clarsimp
      apply (metis Seq.prems(7) list.sel(1) process_inner.distinct(1) qualifyPlace_simps(1) qualifyPlace_simps(3))
      apply clarsimp
          apply (metis Seq.hyps(2) Seq.prems(1,7,8) fromOpenIn_def pgDefined.simps(4) place.disc(4) place_port.simps(2)
          place_side.simps portSetSide_side qualifyPlace_simps(3,4,5) unqualify_qualify_place_inv x2.edge_to_pg)
      apply clarsimp
      apply (metis "2"(3) Seq.prems(7) list.sel(1) process_inner.distinct(1) qualifyPlace_simps(1) qualifyPlace_simps(3))
      apply clarsimp
      apply (metis Seq.prems(7) list.sel(1) process_inner.distinct(1) qualifyPlace_simps(1) qualifyPlace_simps(3))
      apply clarsimp
       apply (metis Seq.prems(7) list.sel(1) process_inner.distinct(1) qualifyPlace_simps(1) qualifyPlace_simps(3))
      using 2 that(2) apply blast
      done
  qed
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using Seq.hyps(1) Seq.prems(1,4,6,7,8)
      by (metis (no_types, lifting) pgDefined.simps(4) imageE nodePlacesE place.discI(1) qualifyPlace_simps(5) unqualifyEdge_simps(3)
          unqualify_qualify_edge_inv unqualify_qualify_place_inv x1.edge_to_pg)
  next
    case 2
    then show ?thesis
      using Seq.hyps(2) Seq.prems(1,4,6,7,8)
      by (metis (no_types, lifting) pgDefined.simps(4) image_iff qualifyPlace_simps(3) qualifyPlace_simps(5) unqualifyEdge_simps(3)
          unqualify_qualify_edge_inv unqualify_qualify_place_inv x2.edge_to_pg)
  next
    case 3
    then show ?thesis
      apply (subgoal_tac  "edge_from e1b = edge_from e2b")
      apply (subgoal_tac  "e1a = e2a")
        apply (metis Seq.prems(4,6) edge.expand)
       apply (rule pgConstruct_edge_noMerge_open[where p = "edge_to e1a" and x = x1])
      using Seq.prems(1) apply simp
      using x1.edge_to_pg apply blast
           apply assumption
      apply (rule refl)
      apply assumption
        apply (metis place_port.simps(2) portSetSide_absorb)
      apply simp
      using Seq.hyps(2) Seq.prems(1,4,6,7,8)
       apply (metis pgDefined.simps(4) pgConstruct_edge_carries_label place_port.simps(2)
          portSetSide_label qualifyPlace_simps(5) resource_neq(11))
      by (metis Seq.hyps(2) Seq.prems(1,4,6,7,8) pgDefined.simps(4) qualifyPlace_simps(3,5) unqualify_qualify_place_inv x2.edge_to_pg)
  qed
next
  case (Swap x1 x2a)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Par x1 x2)

    let ?shift =
      "shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))
                 (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"

    consider
      n where "n \<in> qualifyNode ParL ` set (pg_nodes (pgConstruct x1))" and "p \<in> set (nodePlaces n)"
    | n where "n \<in> qualifyNode ParR ` set (pg_nodes (pgConstruct x2))" and "p \<in> set (nodePlaces n)"
      using Par.prems(2,7) pgraphPlaces_ground in_nodes_juxtaposeE
      by (metis (no_types, lifting) list.set_map pgConstruct.simps(3) qualifyPortGraph_simps(2))
    then consider
      n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParL p'"
    | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParR p'"
      by (cases ; metis (no_types, opaque_lifting) imageE list.set_map qualifyNode_places)
    then consider
      n p' where "n \<in> set (pg_nodes (pgConstruct x1))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParL p'"
             and "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
             and "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
    | n p' where "n \<in> set (pg_nodes (pgConstruct x2))" and "p' \<in> set (nodePlaces n)" and "p = qualifyPlace ParR p'"
             and "e1 \<in> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
             and "e2 \<in> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
    proof cases
      case 1
      moreover have "e1 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e1 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "hd (place_name (edge_to e1)) = ParR"
          using Par.prems(3,4,7) by clarsimp
        moreover have "hd (place_name (edge_to e1)) = ParL"
          using 1 Par.prems(4) by clarsimp
        ultimately show False
          by fastforce
      qed
      moreover have "e2 \<in> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
      proof (rule ccontr)
        assume "e2 \<notin> qualifyEdge ParL ` set (pg_edges (pgConstruct x1))"
        then have "hd (place_name (edge_to e2)) = ParR"
          using Par.prems(5,6,7) by clarsimp
        moreover have "hd (place_name (edge_to e2)) = ParL"
          using 1 Par.prems(6) by clarsimp
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(1))
    next
      case 2
      moreover have "e1 \<in>  ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e1 \<notin> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "hd (place_name (edge_to e1)) = ParL"
          using Par.prems(3,4,7) by (clarsimp simp add: image_comp)
        moreover have "hd (place_name (edge_to e1)) = ParR"
          using 2 Par.prems(4) by clarsimp
        ultimately show False
          by fastforce
      qed
      moreover have
        "e2 \<in> ?shift ` qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
      proof (rule ccontr)
        assume "e2 \<notin> shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))
           (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1)))) `
          qualifyEdge ParR ` set (pg_edges (pgConstruct x2))"
        then have "hd (place_name (edge_to e2)) = ParL"
          using Par.prems(5,6,7) by (clarsimp simp add: image_comp)
        moreover have "hd (place_name (edge_to e2)) = ParR"
          using 2 Par.prems(6) by clarsimp
        ultimately show False
          by fastforce
      qed
      ultimately show ?thesis
        by (rule that(2))
    qed
    then show ?case
    proof cases
      case 1
      then show ?thesis
        using Par.hyps(1) Par.prems(1,4,6,7,8)
        by (metis (no_types, lifting) pgDefined.simps(5) imageE nodePlacesE place.discI(1) port_graph.edge_to_pg port_graph_flow.axioms(1)
            port_graph_flow_pgConstruct qualifyPlace_simps(5) unqualifyEdge_simps(3) unqualify_qualify_edge_inv unqualify_qualify_place_inv)
    next
      case 2
      then show ?thesis
        apply clarsimp
        apply (rule arg_cong[where f = "shiftOpenInEdge _ _"])
        apply (rule arg_cong[where f = "qualifyEdge _"])
        apply (rule Par.hyps(2)[where p = p'])
        using Par.prems(1) pgDefined.simps(5) apply blast
              apply fastforce
             apply assumption
            apply (smt (verit, best) "2"(3) Par.prems(4,7) place.disc(2) place.exhaust_sel qualifyEdge_simps(3) shiftOpenInEdge_simps(2)
            shiftOpenPlace.simps(1) shiftOpenPlace_ground(1) unqualify_qualify_place_inv)
             apply assumption
        apply (metis "2"(3) Par.prems(6,7) qualifyEdge_simps(3) shiftOpenInEdge_simps(2) shiftOpenPlace_ground(1,2) unqualify_qualify_place_inv)
        apply simp
        by (metis "2"(3) Par.prems(8) qualifyPlace_simps(5))
    qed
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
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Erase x)
  then show ?case by simp
next
  case (Represent x)
  then show ?case by simp
next
  case (Apply x1 x2a)
  then show ?case by simp
next
  case (Repeat x1 x2a)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
next
  case (Close x1 x2a)
  then show ?case by simp
next
  case (Once x1 x2a)
  then show ?case by simp
next
  case (Forget x)
  then show ?case
    apply (simp del: parallelPorts.simps)
    apply (elim disjE imageE ; clarsimp simp add: in_set_zip)
    done
qed

text\<open>Any place with no edges touching it must carry a copyable resource and be an open input or ground output\<close>
lemma pgConstruct_edge_none:
  assumes "pgDefined x"
      and "valid x"
      and "p \<in> set (pgraphPlaces (pgConstruct x))"
      and "\<And>e. e \<in> set (pg_edges (pgConstruct x)) \<Longrightarrow> edge_from e \<noteq> p"
      and "\<And>e. e \<in> set (pg_edges (pgConstruct x)) \<Longrightarrow> edge_to e \<noteq> p"
      and "   (place_ground p \<and> port.side (place_port p) = In)
            \<or> (place_open p \<and> port.side (place_port p) = Out)
          \<Longrightarrow> port.label (place_port p) \<noteq> Anything"
    shows " ( (\<exists>a. port.label (place_port p) = Copyable a) \<or> (\<exists>a b. port.label (place_port p) = Repeatable a b))
          \<and> ( (place_open p \<and> port.side (place_port p) = In) \<or> (place_ground p \<and> port.side (place_port p) = Out))"
  using assms
proof (induct x arbitrary: p)
  case (Primitive x1 x2a x3 x4)

  have
    " set (pgraphPlaces (pgConstruct (Primitive x1 x2a x3 x4)))
    = edge_from ` set (pg_edges (pgConstruct (Primitive x1 x2a x3 x4))) \<union>
      edge_to ` set (pg_edges (pgConstruct (Primitive x1 x2a x3 x4)))"
    by (simp del: parallelPorts.simps add: image_comp image_Un case_prod_beta) blast
  then consider
    "p \<in> edge_from ` set (pg_edges (pgConstruct (Primitive x1 x2a x3 x4)))"
  | "p \<in> edge_to ` set (pg_edges (pgConstruct (Primitive x1 x2a x3 x4)))"
    using Primitive(3) by blast
  then have False
    using Primitive(4,5) by blast
  then show ?case ..
next
  case (Identity x)

  have
    " set (pgraphPlaces (pgConstruct (Identity x)))
    = edge_from ` set (pg_edges (pgConstruct (Identity x))) \<union>
      edge_to ` set (pg_edges (pgConstruct (Identity x)))"
    by (simp del: parallelPorts.simps add: image_comp image_Un case_prod_beta)
  then consider
    "p \<in> edge_from ` set (pg_edges (pgConstruct (Identity x)))"
  | "p \<in> edge_to ` set (pg_edges (pgConstruct (Identity x)))"
    using Identity(3) by blast
  then have False
    using Identity(4,5) by blast
  then show ?case ..
next
  case (Seq x1 x2)

  have pgf1: "port_graph_flow (pgConstruct x1)"
    using Seq.prems(1) pgDefined.simps(4) port_graph_flow_pgConstruct
    by blast
  then interpret x1: port_graph_flow "pgConstruct x1" .

  have pgf2: "port_graph_flow (pgConstruct x2)"
    using Seq.prems(1) pgDefined.simps(4) port_graph_flow_pgConstruct
    by blast
  then interpret x2: port_graph_flow "pgConstruct x2" .

  consider
    p' where "p' \<in> set (pgraphPlaces (pgConstruct x1))" and "p = qualifyPlace SeqL p'" and "place_open p \<Longrightarrow> port.side (place_port p) = In"
  | p' where "p' \<in> set (pgraphPlaces (pgConstruct x2))" and "p = qualifyPlace SeqR p'" and "place_open p \<Longrightarrow> port.side (place_port p) = Out"
    using Seq.prems(3)
    apply (simp add: pgraphPlaces_seqPortGraphs del: pgraphPlaces.simps seqPortGraphs.simps)
    using that
    by (smt (verit) In_process_side_def Out_process_side_def image_iff mem_Collect_eq not_place_open process_side.exhaust)
  note case_split = this

  have False
    if contra: "\<And>a. port.label (place_port p) \<noteq> Resource.Copyable a"
               "\<And>a b. port.label (place_port p) \<noteq> Resource.Repeatable a b"
    \<comment> \<open>Proof by contradiction so we can use other linearity theorems within\<close>
  proof (cases rule: case_split)
    case 1
    moreover have "edge_from e \<noteq> p'"
      if p'_in: "p' \<in> set (pgraphPlaces (pgConstruct x1))"
     and p: "p = qualifyPlace SeqL p'"
     and e: "e \<in> set (pg_edges (pgConstruct x1))"
     for e
    proof
      assume e_from: "edge_from e = p'"

      have "\<exists>e'. edge_from e' = p \<and> e' \<in> set (pg_edges (pgConstruct (Seq x1 x2)))"
        \<comment> \<open>If the place were to be in x1 and has an adjacent edge, then that edge would in some
            form appear in the composed port graph\<close>
      proof (cases "place_ground (edge_to e)")
        case True
        then show ?thesis
          \<comment> \<open>If the edge goes to a ground place then it is simply passed on to the composition\<close>
           apply simp
           apply (rule_tac x = "qualifyEdge SeqL e" in exI)
           apply (rule conjI)
          using that(2) e_from apply simp
           apply (rule disjI2, rule disjI1)
          using that(3)
          apply (simp add: disconnectFromPlaces_def)
          by (metis (mono_tags, lifting) calculation(3) e_from image_iff in_out_distinct mem_Collect_eq not_place_open p place.disc(2)
              place_port.simps(2) qualifyPlace_simps(3))
      next
        case False

        have "\<exists>f. f \<in> set (pg_edges (pgConstruct x2)) \<and> edge_from f = OpenPort (portSetSide In (place_port (edge_to e)))"
          \<comment> \<open>If it is open then there must be a corresponding edge in x2 with which the one in x1 will compose\<close>
        proof -
          have "\<And>a. \<lbrakk>a \<in> set (pg_ports (pgConstruct x1)); port.side a = Out\<rbrakk> \<Longrightarrow> portSetSide In a \<in> set (pg_ports (pgConstruct x2))"
            \<comment> \<open>Any output port of x1 corresponds to an input port of x2\<close>
            (* TODO extract as general theorem *)
            using Seq.prems(1,2) by (fastforce simp add: pgConstruct_ports)
          then have counterpart: "portSetSide In (place_port (edge_to e)) \<in> set (pg_ports (pgConstruct x2))"
            \<comment> \<open>So the edge's output has a corresponding port in x2\<close>
            by (metis (full_types) False In_process_side_def Out_process_side_def e edge_in_flowI(3) not_place_ground place_side.elims
                x1.edge_to_pg process_side.exhaust x1.edge_to_cases x1.open_port_pg)

          have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x2)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide In (place_port (edge_to e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x2)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide In (place_port (edge_to e)))\<rbrakk>
            \<Longrightarrow> (\<exists>a. port.label (place_port (OpenPort (portSetSide In (place_port (edge_to e))))) = Resource.Copyable a)
              \<or> (\<exists>a b. port.label (place_port (OpenPort (portSetSide In (place_port (edge_to e))))) = Resource.Repeatable a b)"
            \<comment> \<open>So the induction hypothesis applies to that port in x2\<close>
             apply (cut_tac Seq.hyps(2)[of "OpenPort (portSetSide In (place_port (edge_to e)))", THEN conjunct1])
                    apply simp
            using Seq.prems(1) apply simp
            using Seq.prems(2) apply simp
            using Seq.prems(3) apply simp
            using counterpart apply simp
            apply blast
            apply blast
             apply auto[1]
            done
          moreover consider
            "port.label (place_port (OpenPort (portSetSide In (place_port (edge_to e))))) = port.label (place_port p)"
          | "port.label (place_port (OpenPort (portSetSide In (place_port (edge_to e))))) = Anything"
            \<comment> \<open>Whose label is the same as p by linearity or the anything resource\<close>
            using contra pgConstruct_edge_carries_label e e_from Seq.prems(1,2) p
            by (metis pgDefined.simps(4) place_port.simps(2) portSetSide_label qualifyPlace_simps(5))
          ultimately have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x2)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide In (place_port (edge_to e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x2)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide In (place_port (edge_to e)))\<rbrakk>
            \<Longrightarrow> (\<exists>a. port.label (place_port p) = Resource.Copyable a) \<or> (\<exists>a b. port.label (place_port p) = Resource.Repeatable a b)"
            \<comment> \<open>But the anything case leads to a contradiction\<close>
            by (smt (verit, best) resource_neq(8,11))
          then have "\<exists>f \<in> set (pg_edges (pgConstruct x2)).
              edge_from f = OpenPort (portSetSide In (place_port (edge_to e)))
            \<or> edge_to f = OpenPort (portSetSide In (place_port (edge_to e)))"
            \<comment> \<open>So by contradiction assumption there must be an adjacent edge to that port in x2\<close>
            using contra by blast
          then show ?thesis
            \<comment> \<open>Finally, because of the port's side, that edge can only originate there\<close>
            using x2.edge_to_open
            by (metis edge_in_flowI(3) in_out_distinct place.disc(4) place_port.simps(2) place_side.simps portSetSide_side)
        qed
        then obtain f where f: "f \<in> set (pg_edges (pgConstruct x2))" "edge_from f = OpenPort (portSetSide In (place_port (edge_to e)))"
          by metis

        obtain xs
         where xs: "Mapping.lookup (edgesByOpenTo (map (qualifyEdge SeqL) (pg_edges (pgConstruct x1))))
                (portSetSide Out (place_port (edge_to e))) = Some xs"
          using edgesByOpenTo_Some_ex e False x1.edge_to_cases
          by (smt (verit, best) In_process_side_def Out_process_side_def edge_in_flowI(3,4) edgesByOpenTo_qualify lookup_map_values option.map(2)
              place_side.simps portSetSide_same process_side.exhaust)

        obtain ys
         where ys: "Mapping.lookup (edgesByOpenFrom (map (qualifyEdge SeqR) (pg_edges (pgConstruct x2))))
                (portSetSide In (place_port (edge_to e))) = Some ys"
          using edgesByOpenFrom_Some_ex f
          by (metis (mono_tags, opaque_lifting) image_iff list.set_map place.disc(4) place_port.simps(2) qualifyEdge_simps(2) qualifyPlace.simps(2))

        show ?thesis
          using False
          apply simp
           apply (rule_tac x = "Edge (edge_from (qualifyEdge SeqL e)) (edge_to (qualifyEdge SeqR f))" in exI)
           apply (rule conjI)
          using that(2) e_from apply simp
          apply (rule disjI1)
          apply (rule_tac p = "place_port (edge_to e)" and xs = "map edge_from xs" and ys = "map edge_to ys" in edgesFromPortMapping_setI)
          using that(3) x1.edge_to_pg x1.open_port_pg x1.edge_to_open
               apply (smt (verit, ccfv_SIG) In_process_side_def Out_process_side_def edge_in_flowI(3) filter_set member_filter not_place_ground
              place_side.elims process_side.exhaust)
              prefer 5
              apply (rule refl)
          apply (simp add: lookup_map_values xs)
            apply (simp add: lookup_map_values ys)
          using xs edgesByOpenTo_in_result x1.edge_to_open that(3)
           apply (smt (verit, ccfv_SIG) In_process_side_def Out_process_side_def edge_in_flowI(1,2) imageI image_set place_side.elims port.expand
              portSetSide_index portSetSide_label portSetSide_side process_side.exhaust qualifyEdge_simps(3) qualifyPlace_rename renamePlace_simps(2) x1.edge_to_cases)
          using ys edgesByOpenFrom_in_result f
          by (metis (no_types, lifting) image_eqI list.set_map place.disc(4) place_port.simps(2) qualifyEdge_simps(2) qualifyPlace_simps(2))
      qed
      then show False
        using Seq.prems(4) by metis
    qed
    moreover have "edge_to e \<noteq> p'"
      if p'_in: "p' \<in> set (pgraphPlaces (pgConstruct x1))"
     and p: "p = qualifyPlace SeqL p'"
     and e: "e \<in> set (pg_edges (pgConstruct x1))"
     for e
    proof
      assume e_to: "edge_to e = p'"

      have "\<exists>e'. edge_to e' = p \<and> e' \<in> set (pg_edges (pgConstruct (Seq x1 x2)))"
        \<comment> \<open>If the place were to be in x1 and has an adjacent edge, then that edge would in some
            form appear in the composed port graph\<close>
      proof (cases "place_ground (edge_to e)")
        case True
        then show ?thesis
          \<comment> \<open>If it is a ground place then the edge is simply passed on to the composition\<close>
           apply simp
           apply (rule_tac x = "qualifyEdge SeqL e" in exI)
           apply (rule conjI)
          using that(2) e_to apply simp
           apply (rule disjI2, rule disjI1)
          using that(3)
          apply (simp add: disconnectFromPlaces_def)
          by (smt (verit, ccfv_SIG) edge_in_flowI(2) image_iff in_out_distinct mem_Collect_eq not_place_open place.distinct(1)
              place_ground_def place_port.simps(2) place_side.simps qualifyPlace.simps(2) unqualify_qualify_place_inv x1.edge_from_open)
      next
        case False
        then have False
          \<comment> \<open>To appear in the composition it needs to be an input place if open, but an edge
              going into it means it must be an output place\<close>
          using x1.edge_to_open e e_to p 1(3)
          by (metis edge_in_flowI(3) in_out_distinct place.exhaust_disc place_side.simps qualifyPlace_simps(2))
        then show ?thesis ..
      qed
      then show False
        using Seq.prems(5) by metis
    qed
    ultimately show ?thesis
      using Seq.prems(1,2,6) Seq.hyps(1)[of p'] contra by force
  next
    case 2
    moreover have "edge_to e \<noteq> p'"
      if p'_in: "p' \<in> set (pgraphPlaces (pgConstruct x2))"
     and p: "p = qualifyPlace SeqR p'"
     and e: "e \<in> set (pg_edges (pgConstruct x2))"
     for e
    proof
      assume e_to: "edge_to e = p'"

      have "\<exists>e'. edge_to e' = p \<and> e' \<in> set (pg_edges (pgConstruct (Seq x1 x2)))"
        \<comment> \<open>If the place were to be in x2 and has an adjacent edge, then that edge would in some
            form appear in the composed port graph\<close>
      proof (cases "place_ground (edge_from e)")
        case True
        then show ?thesis
          \<comment> \<open>If it is a ground place then the edge is simply passed on to the composition\<close>
           apply simp
           apply (rule_tac x = "qualifyEdge SeqR e" in exI)
           apply (rule conjI)
          using that(2) e_to apply simp
           apply (rule disjI2, rule disjI2)
          using that(3)
          apply (simp add: disconnectFromPlaces_def)
          using e_to 2(3)
          by (metis (mono_tags, lifting) image_iff mem_Collect_eq p place.disc(2) place.exhaust_disc place_port.simps(2) in_out_distinct qualifyPlace_simps(3))
      next
        case False

        have "\<exists>f. f \<in> set (pg_edges (pgConstruct x1)) \<and> edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
          \<comment> \<open>If it is open then there must be a corresponding edge in x1 with which the one in x2 will compose\<close>
        proof -
          have "\<And>a. \<lbrakk>a \<in> set (pg_ports (pgConstruct x2)); port.side a = In\<rbrakk> \<Longrightarrow> portSetSide Out a \<in> set (pg_ports (pgConstruct x1))"
            \<comment> \<open>Any output port of x2 corresponds to an input port of x1\<close>
            (* TODO extract as general theorem *)
            using Seq.prems(1,2) by (fastforce simp add: pgConstruct_ports)
          then have counterpart: "portSetSide Out (place_port (edge_from e)) \<in> set (pg_ports (pgConstruct x1))"
            \<comment> \<open>So the edge's input has a corresponding port in x1\<close>
            by (metis (full_types) False In_process_side_def Out_process_side_def e edge_in_flowI(3,4) not_place_open place_side.simps
                process_side.exhaust x2.edge_from_open x2.edge_from_pg x2.open_port_pg)

          have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)))\<rbrakk>
            \<Longrightarrow> ( (\<exists>a. port.label (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Resource.Copyable a)
                \<or> (\<exists>a b. port.label (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Resource.Repeatable a b))
             \<and> (    place_open (OpenPort (portSetSide Out (place_port (edge_from e))))
                  \<and> port.side (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = In
                \<or> place_ground (OpenPort (portSetSide Out (place_port (edge_from e))))
                  \<and> port.side (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Out)"
            \<comment> \<open>So the induction hypothesis applies to that port in x1\<close>
            apply (cut_tac Seq.hyps(1)[of "OpenPort (portSetSide Out (place_port (edge_from e)))"])
            apply simp (* TODO why is this not just going through using intro? *)
            using Seq.prems(1,2) apply simp
            using Seq.prems(1,2) apply simp
            using Seq.prems(1,2) apply simp
            using counterpart apply simp
            apply metis
             apply metis
            using Seq.prems(1,6) calculation(3) e e_to p apply clarsimp
            by (metis (full_types) In_process_side_def Out_process_side_def edge_in_flowI(3,4) pgConstruct_edge_carries_label
                place_side.simps process_side.exhaust resource_neq(11) x2.edge_to_cases)
          then have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)))\<rbrakk>
            \<Longrightarrow> False"
            \<comment> \<open>Its conclusion asks for an open place to be ground, so the assumptions must not be true\<close>
            by simp
          then have "\<exists>f \<in> set (pg_edges (pgConstruct x1)).
              edge_from f = OpenPort (portSetSide Out (place_port (edge_from e)))
            \<or> edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
            \<comment> \<open>Which guarantees the existence of the needed witness\<close>
            by blast
          then show ?thesis
            \<comment> \<open>Finally, because of the port's side, that edge can only originate there\<close>
            using x1.edge_from_open edge_in_flowI(2) by force
        qed
        then obtain f where f: "f \<in> set (pg_edges (pgConstruct x1))" "edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
          by metis

        obtain xs
         where xs: "Mapping.lookup (edgesByOpenTo (map (qualifyEdge SeqL) (pg_edges (pgConstruct x1))))
                (portSetSide Out (place_port (edge_to f))) = Some xs"
          using edgesByOpenTo_Some_ex f x1.edge_to_cases
          by (smt (verit, del_insts) edgesByOpenTo_qualify lookup_map_values option.map(2) place.disc(4) place_port.simps(2) portSetSide_same portSetSide_side)

        obtain ys
         where ys: "Mapping.lookup (edgesByOpenFrom (map (qualifyEdge SeqR) (pg_edges (pgConstruct x2))))
                (portSetSide In (place_port (edge_to f))) = Some ys"
          using edgesByOpenFrom_Some_ex e False x2.edge_from_cases f(2)
          by (smt (verit, ccfv_SIG) In_process_side_def Out_process_side_def edge_in_flowI(3) edge_in_flowI(4) image_eqI list.set_map place_port.simps(2)
              place_side.simps portSetSide_absorb portSetSide_same process_side.exhaust qualifyEdge_simps(2) qualifyPlace_simps(2))

        show ?thesis
          using False
          apply simp
           apply (rule_tac x = "Edge (edge_from (qualifyEdge SeqL f)) (edge_to (qualifyEdge SeqR e))" in exI)
           apply (rule conjI)
          using that(2) e_to apply simp
          apply (rule disjI1)
          apply (rule_tac p = "place_port (edge_to f)" and xs = "map edge_from xs" and ys = "map edge_to ys" in edgesFromPortMapping_setI)
          using f(1) f(2) port_graph.edge_to_pg x1.port_graph_axioms apply fastforce
              prefer 5
              apply (rule refl)
          apply (simp add: lookup_map_values xs)
            apply (simp add: lookup_map_values ys)
          using xs edgesByOpenTo_in_result f x1.edge_to_cases
          apply (metis (no_types, lifting) image_set place.disc(4) place_port.simps(2) portSetSide_absorb qualifyEdge_simps(3)
              qualifyPlace_rename renamePlace.simps(2) rev_image_eqI)
          using ys edgesByOpenFrom_in_result e f(2) x2.edge_from_cases
          by (smt (verit, ccfv_SIG) In_process_side_def Out_process_side_def edge_in_flowI(1) edge_in_flowI(2) image_eqI list.set_map
              place_port.simps(2) place_side.simps portSetSide_absorb portSetSide_same process_side.exhaust qualifyEdge_simps(2) qualifyPlace_simps(2))
      qed
      then show False
        using Seq.prems(5) by metis
    qed
    moreover have "edge_from e \<noteq> p'"
      if p'_in: "p' \<in> set (pgraphPlaces (pgConstruct x2))"
     and p: "p = qualifyPlace SeqR p'"
     and e: "e \<in> set (pg_edges (pgConstruct x2))"
     for e
    proof
      assume e_from: "edge_from e = p'"

      have "\<exists>e'. edge_from e' = p \<and> e' \<in> set (pg_edges (pgConstruct (Seq x1 x2)))"
        \<comment> \<open>If the place were to be in x2 and has an adjacent edge, then that edge would in some
            form appear in the composed port graph\<close>
      proof (cases "place_ground (edge_from e)")
        case True
        then show ?thesis
          \<comment> \<open>If it is a ground place then the edge is simply passed on to the composition\<close>
           apply simp
           apply (rule_tac x = "qualifyEdge SeqR e" in exI)
           apply (rule conjI)
          using that(2) e_from apply simp
           apply (rule disjI2, rule disjI2)
          using that(3)
          apply (simp add: disconnectFromPlaces_def)
          by (smt (verit) edge_in_flowI(3) image_iff in_out_distinct mem_Collect_eq not_place_open place.disc(2)
              place_port.simps(2) place_side.simps qualifyPlace_simps(2,3) x2.edge_to_open)
      next
        case False
        then have False
          \<comment> \<open>To appear in the composition it needs to be an input place if open, but an edge
              going into it means it must be an output place\<close>
          using x2.edge_to_open e e_from p 2(3) x2.edge_from_open
          by (metis edge_in_flowI(2) in_out_distinct place.exhaust_disc place_side.elims qualifyPlace_simps(2))
        then show ?thesis ..
      qed
      then show False
        using Seq.prems(4) by metis
    qed
    ultimately show ?thesis
      using Seq.prems(1,2,6) Seq.hyps(2)[of p'] contra by force
  qed
  moreover have False
    if contra: "place_open p \<and> port.side (place_port p) = Out \<or> place_ground p \<and> port.side (place_port p) = In"
    using contra
    apply (cases rule: case_split ; elim disjE ; clarsimp simp del: pgraphPlaces.simps)
  proof - (* TODO Isarify the above specific case split *)
    fix p'
    assume p'_in: "p' \<in> set (pgraphPlaces (pgConstruct x1))"
       and p: "p = qualifyPlace SeqL p'"
       and p'_ground: "place_ground p'"
       and p'_In: "port.side (place_port p') = In"

    have "\<And>e. e \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_from e \<noteq> p'"
      using p'_In p'_ground x1.edge_from_ground
      by (metis edge_in_flowI(1) in_out_distinct place_side.simps)
    moreover have "edge_to e \<noteq> p'" if "e \<in> set (pg_edges (pgConstruct x1))" for e
    proof
      assume e_to: "edge_to e = p'"
      have "\<exists>f. f \<in> set (pg_edges (pgConstruct (Seq x1 x2))) \<and> edge_to f = qualifyPlace SeqL p'"
        using p'_ground
        apply simp
        apply (rule_tac x = "qualifyEdge SeqL e" in exI)
        apply (rule conjI)
         apply (rule disjI2, rule disjI1)
         apply (simp add: disconnectFromPlaces_def)
        using e_to that x1.edge_from_cases
         apply clarsimp
         apply (smt (verit, del_insts) edge_in_flowI(1) edge_in_flowI(2) image_iff in_out_distinct mem_Collect_eq not_place_open
            place.distinct(1) place_ground_def place_port.simps(2) process_side.exhaust qualifyPlace_simps(2,4))
        using e_to apply simp
        done
      then show False
        using Seq.prems(5) p by blast
    qed
    ultimately have "port.side (place_port p') = Out"
      using Seq.prems(1,2,6) Seq.hyps(1)[of p'] p'_ground p'_in that
      using in_out_distinct p by force
    then show False
      using p'_In by simp
  next
    assume p_in: "p \<in> set (pgraphPlaces (pgConstruct x2))"
       and p_open: "place_open p"
       and p_Out: "port.side (place_port p) = Out"

    have "\<And>e. e \<in> set (pg_edges (pgConstruct x2)) \<Longrightarrow> edge_from e \<noteq> p"
      using p_Out p_open x2.edge_from_open edge_in_flowI(2) by fastforce
    moreover have "edge_to e \<noteq> p" if e: "e \<in> set (pg_edges (pgConstruct x2))" for e
    (* TODO reference-adjusted copy of the above edge_to x2 proof *)
    proof
      assume e_to: "edge_to e = p"

      have "\<exists>e'. edge_to e' = p \<and> e' \<in> set (pg_edges (pgConstruct (Seq x1 x2)))"
        \<comment> \<open>If the place were to be in x2 and has an adjacent edge, then that edge would in some
            form appear in the composed port graph\<close>
      proof (cases "place_ground (edge_from e)")
        case True
        then show ?thesis
          \<comment> \<open>If it is a ground place then the edge is simply passed on to the composition\<close>
           apply simp
           apply (rule_tac x = "qualifyEdge SeqR e" in exI)
           apply (rule conjI)
          using e_to p_open apply simp
           apply (rule disjI2, rule disjI2)
          apply (simp add: disconnectFromPlaces_def)
          using e_to e p_Out
          by (smt (verit) image_iff mem_Collect_eq place.disc(2) place_open_def place_port.simps(2) in_out_distinct qualifyPlace_simps(2,4))
      next
        case False

        have "\<exists>f. f \<in> set (pg_edges (pgConstruct x1)) \<and> edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
          \<comment> \<open>If it is open then there must be a corresponding edge in x1 with which the one in x2 will compose\<close>
        proof -
          have "\<And>a. \<lbrakk>a \<in> set (pg_ports (pgConstruct x2)); port.side a = In\<rbrakk> \<Longrightarrow> portSetSide Out a \<in> set (pg_ports (pgConstruct x1))"
            \<comment> \<open>Any output port of x2 corresponds to an input port of x1\<close>
            (* TODO extract as general theorem *)
            using Seq.prems(1,2) Seq.prems(3) by (fastforce simp add: pgConstruct_ports)
          then have counterpart: "portSetSide Out (place_port (edge_from e)) \<in> set (pg_ports (pgConstruct x1))"
            \<comment> \<open>So the edge's input has a corresponding port in x1\<close>
            by (metis False e_to edge_in_flowI(4) p_Out place_side.elims x2.edge_from_pg x2.open_port_pg x2.edge_from_cases that)

          have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)))\<rbrakk>
            \<Longrightarrow> ( (\<exists>a. port.label (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Resource.Copyable a)
                \<or> (\<exists>a b. port.label (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Resource.Repeatable a b))
             \<and> (    place_open (OpenPort (portSetSide Out (place_port (edge_from e))))
                  \<and> port.side (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = In
                \<or> place_ground (OpenPort (portSetSide Out (place_port (edge_from e))))
                  \<and> port.side (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Out)"
            \<comment> \<open>So the induction hypothesis applies to that port in x1\<close>
            apply (cut_tac Seq.hyps(1)[of "OpenPort (portSetSide Out (place_port (edge_from e)))"])
            apply simp (* TODO why is this not just going through using intro? *)
            using Seq.prems(1,2) apply simp
            using Seq.prems(1,2) apply simp
            using Seq.prems(1,2) apply simp
            using counterpart apply simp
            apply metis
             apply metis
            using Seq.prems(1,6) e_to p_Out p_open that
            by (metis pgDefined.simps(4) pgConstruct_edge_carries_label place_port.simps(2) portSetSide_label resource_neq(11))
          then have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)))\<rbrakk>
            \<Longrightarrow> False"
            \<comment> \<open>Its conclusion asks for an open place to be ground, so the assumptions must not be true\<close>
            by simp
          then have "\<exists>f \<in> set (pg_edges (pgConstruct x1)).
              edge_from f = OpenPort (portSetSide Out (place_port (edge_from e)))
            \<or> edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
            \<comment> \<open>Which guarantees the existence of the needed witness\<close>
            by blast
          then show ?thesis
            \<comment> \<open>Finally, because of the port's side, that edge can only originate there\<close>
            using x1.edge_from_open
            by (metis edge_in_flowI(2) in_out_distinct place.disc(4) place_port.simps(2) place_side.simps portSetSide_side)
        qed
        then obtain f where f: "f \<in> set (pg_edges (pgConstruct x1))" "edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
          by metis

        obtain xs
         where xs: "Mapping.lookup (edgesByOpenTo (map (qualifyEdge SeqL) (pg_edges (pgConstruct x1))))
                (portSetSide Out (place_port (edge_to f))) = Some xs"
          using edgesByOpenTo_Some_ex f x1.edge_to_cases
          by (metis (mono_tags, opaque_lifting) image_iff list.set_map place.disc(4) place_port.simps(2) portSetSide_same
              portSetSide_side qualifyEdge_simps(3) qualifyPlace.simps(2))

        obtain ys
         where ys: "Mapping.lookup (edgesByOpenFrom (map (qualifyEdge SeqR) (pg_edges (pgConstruct x2))))
                (portSetSide In (place_port (edge_to f))) = Some ys"
          using edgesByOpenFrom_Some_ex e False x2.edge_from_cases f(2)
          by (metis (no_types, lifting) e_to edge_in_flowI(4) image_eqI list.set_map p_Out place_port.simps(2) place_side.simps
              portSetSide_absorb portSetSide_same qualifyEdge_simps(2) qualifyPlace_simps(2))

        show ?thesis
          using False
          apply simp
           apply (rule_tac x = "Edge (edge_from (qualifyEdge SeqL f)) (edge_to (qualifyEdge SeqR e))" in exI)
           apply (rule conjI)
          using p_open e_to apply simp
          apply (rule disjI1)
          apply (rule_tac p = "place_port (edge_to f)" and xs = "map edge_from xs" and ys = "map edge_to ys" in edgesFromPortMapping_setI)
          using f(1) f(2) port_graph.edge_to_pg x1.port_graph_axioms apply fastforce
              prefer 5
              apply (rule refl)
          apply (simp add: lookup_map_values xs)
            apply (simp add: lookup_map_values ys)
          using xs edgesByOpenTo_in_result f x1.edge_to_cases
          apply (metis (no_types, lifting) image_eqI list.set_map place.disc(4) place_port.simps(2) portSetSide_absorb qualifyEdge_simps(3) qualifyPlace_simps(2))
          using ys edgesByOpenFrom_in_result e f(2) x2.edge_from_cases
          by (metis (no_types, lifting) e_to edge_in_flowI(4) image_eqI list.set_map p_Out place_port.simps(2)
              place_side.simps portSetSide_absorb portSetSide_same qualifyEdge_simps(2) qualifyPlace_simps(2))
      qed
      then show False
        using Seq.prems(5) by metis
    qed
    ultimately have "port.side (place_port p) = In"
      using Seq.prems(1,2,6) Seq.hyps(2)[of p] p_open p_in that by force
    then show False
      using p_Out by simp
  next
    fix p'
    assume p'_in: "p' \<in> set (pgraphPlaces (pgConstruct x2))"
       and p: "p = qualifyPlace SeqR p'"
       and p'_ground: "place_ground p'"
       and p'_In: "port.side (place_port p') = In"

    have "\<And>e. e \<in> set (pg_edges (pgConstruct x2)) \<Longrightarrow> edge_from e \<noteq> p'"
      using p'_In p'_ground x2.edge_from_ground
      by (metis edge_in_flowI(1) in_out_distinct place_side.simps)
    moreover have "edge_to e \<noteq> p'" if e: "e \<in> set (pg_edges (pgConstruct x2))" for e
    proof
      assume e_to: "edge_to e = p'"

      have "\<exists>e'. edge_to e' = p \<and> e' \<in> set (pg_edges (pgConstruct (Seq x1 x2)))"
        \<comment> \<open>If the place were to be in x2 and has an adjacent edge, then that edge would in some
            form appear in the composed port graph\<close>
      proof (cases "place_ground (edge_from e)")
        case True
        then show ?thesis
          \<comment> \<open>If it is a ground place then the edge is simply passed on to the composition\<close>
           apply simp
           apply (rule_tac x = "qualifyEdge SeqR e" in exI)
           apply (rule conjI)
          using p e_to apply simp
          apply (rule disjI2, rule disjI2)
          using p'_In e p'_ground e_to
          apply (simp add: disconnectFromPlaces_def)
          by (metis (no_types, lifting) image_iff place.disc(2) qualifyPlace_simps(3))
      next
        case False

        have "\<exists>f. f \<in> set (pg_edges (pgConstruct x1)) \<and> edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
          \<comment> \<open>If it is open then there must be a corresponding edge in x1 with which the one in x2 will compose\<close>
        proof -
          have "\<And>a. \<lbrakk>a \<in> set (pg_ports (pgConstruct x2)); port.side a = In\<rbrakk> \<Longrightarrow> portSetSide Out a \<in> set (pg_ports (pgConstruct x1))"
            \<comment> \<open>Any output port of x2 corresponds to an input port of x1\<close>
            (* TODO extract as general theorem *)
            using Seq.prems(1,2) by (fastforce simp add: pgConstruct_ports)
          then have counterpart: "portSetSide Out (place_port (edge_from e)) \<in> set (pg_ports (pgConstruct x1))"
            \<comment> \<open>So the edge's input has a corresponding port in x1\<close>
            by (metis False e_to edge_in_flowI(3) not_place_ground p'_In place_side.elims x2.edge_from_pg x2.open_port_pg x2.edge_from_open that)

          have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)))\<rbrakk>
            \<Longrightarrow> ( (\<exists>a. port.label (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Resource.Copyable a)
                \<or> (\<exists>a b. port.label (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Resource.Repeatable a b))
             \<and> (    place_open (OpenPort (portSetSide Out (place_port (edge_from e))))
                  \<and> port.side (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = In
                \<or> place_ground (OpenPort (portSetSide Out (place_port (edge_from e))))
                  \<and> port.side (place_port (OpenPort (portSetSide Out (place_port (edge_from e))))) = Out)"
            \<comment> \<open>So the induction hypothesis applies to that port in x1\<close>
            apply (cut_tac Seq.hyps(1)[of "OpenPort (portSetSide Out (place_port (edge_from e)))"])
            apply simp (* TODO why is this not just going through using intro? *)
            using Seq.prems(1,2) apply simp
            using Seq.prems(1,2) apply simp
            using Seq.prems(1,2) apply simp
            using counterpart apply simp
            apply metis
             apply metis
            using Seq.prems(1,6) e_to that contra p
            by (metis pgDefined.simps(4) pgConstruct_edge_carries_label place_port.simps(2)
                portSetSide_label qualifyPlace_simps(5) resource_neq(11))
          then have
            " \<lbrakk>\<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_from ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)));
               \<And>ea. ea \<in> set (pg_edges (pgConstruct x1)) \<Longrightarrow> edge_to ea \<noteq> OpenPort (portSetSide Out (place_port (edge_from e)))\<rbrakk>
            \<Longrightarrow> False"
            \<comment> \<open>Its conclusion asks for an open place to be ground, so the assumptions must not be true\<close>
            by simp
          then have "\<exists>f \<in> set (pg_edges (pgConstruct x1)).
              edge_from f = OpenPort (portSetSide Out (place_port (edge_from e)))
            \<or> edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
            \<comment> \<open>Which guarantees the existence of the needed witness\<close>
            by blast
          then show ?thesis
            \<comment> \<open>Finally, because of the port's side, that edge can only originate there\<close>
            using x1.edge_from_open
            by (metis edge_in_flowI(2) in_out_distinct place.disc(4) place_port.simps(2) place_side.elims portSetSide_side)
        qed
        then obtain f where f: "f \<in> set (pg_edges (pgConstruct x1))" "edge_to f = OpenPort (portSetSide Out (place_port (edge_from e)))"
          by metis

        obtain xs
         where xs: "Mapping.lookup (edgesByOpenTo (map (qualifyEdge SeqL) (pg_edges (pgConstruct x1))))
                (portSetSide Out (place_port (edge_to f))) = Some xs"
          using edgesByOpenTo_Some_ex f x1.edge_to_cases
          by (metis (no_types, lifting) image_iff list.set_map place.disc(4) place_port.simps(2) portSetSide_absorb qualifyEdge_simps(3) qualifyPlace_simps(2))

        obtain ys
         where ys: "Mapping.lookup (edgesByOpenFrom (map (qualifyEdge SeqR) (pg_edges (pgConstruct x2))))
                (portSetSide In (place_port (edge_to f))) = Some ys"
          using edgesByOpenFrom_Some_ex e False x2.edge_from_cases f(2)
          by (metis (no_types, lifting) e_to edge_in_flowI(3) image_eqI list.set_map p'_In place_port.simps(2) place_side.simps
              portSetSide_absorb portSetSide_same qualifyEdge_simps(2) qualifyPlace_simps(2))

        show ?thesis
          using False
          apply simp
           apply (rule_tac x = "Edge (edge_from (qualifyEdge SeqL f)) (edge_to (qualifyEdge SeqR e))" in exI)
           apply (rule conjI)
          using p e_to apply simp
          apply (rule disjI1)
          apply (rule_tac p = "place_port (edge_to f)" and xs = "map edge_from xs" and ys = "map edge_to ys" in edgesFromPortMapping_setI)
          using f(1) f(2) port_graph.edge_to_pg x1.port_graph_axioms apply fastforce
              prefer 5
              apply (rule refl)
          apply (simp add: lookup_map_values xs)
            apply (simp add: lookup_map_values ys)
          using xs edgesByOpenTo_in_result f x1.edge_to_cases
          apply (metis (no_types, lifting) image_eqI list.set_map place.disc(4) place_port.simps(2) portSetSide_absorb qualifyEdge_simps(3) qualifyPlace_simps(2))
          using ys edgesByOpenFrom_in_result e f(2) x2.edge_from_cases
          by (metis (no_types, lifting) e_to edge_in_flowI(3) image_eqI list.set_map p'_In place_port.simps(2) place_side.simps
              portSetSide_absorb portSetSide_same qualifyEdge_simps(2) qualifyPlace_simps(2))
      qed
      then show False
        using Seq.prems(5) by metis
    qed
    ultimately have "port.side (place_port p') = Out"
      using Seq.prems(1,2,6) Seq.hyps(2)[of p'] p'_ground p'_in that p
      using in_out_distinct p by force
    then show False
      using p'_In by simp
  qed
  moreover have
    "\<not>(place_open p \<and> port.side (place_port p) = In \<or> place_ground p \<and> port.side (place_port p) = Out)
    = (place_open p \<and> port.side (place_port p) = Out \<or> place_ground p \<and> port.side (place_port p) = In)"
    for p :: "(process_side, ('a, 'b) resource, process_inner) place"
    by (metis (full_types) not_place_open in_out_distinct process_side.exhaust)
  ultimately show ?case
    by metis
next
  case (Swap x1 x2a)

  have
    " set (pgraphPlaces (pgConstruct (Swap x1 x2a)))
    = edge_from ` set (pg_edges (pgConstruct (Swap x1 x2a))) \<union>
      edge_to ` set (pg_edges (pgConstruct (Swap x1 x2a)))"
    by (simp del: listPorts.simps add: image_comp image_Un case_prod_beta listPorts_append) blast
  then consider
    "p \<in> edge_from ` set (pg_edges (pgConstruct (Swap x1 x2a)))"
  | "p \<in> edge_to ` set (pg_edges (pgConstruct (Swap x1 x2a)))"
    using Swap(3) by blast
  then have False
    using Swap(4,5) by blast
  then show ?case ..
next
  case (Par x1 x2)

  have pgf: "port_graph_flow (pgConstruct (Par x1 x2))"
    using Par by (meson port_graph_flow_pgConstruct)

  let ?shift =
    "shiftOpenInEdge (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))
                 (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"
  let ?shiftIn =
    "shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"
  let ?shiftOut =
    "shiftOpenPlace (\<lambda>s. length (filter (\<lambda>x. port.side x = s) (pg_ports (pgConstruct x1))))"

  have "p \<in> qualifyPlace ParR ` (if port.side (place_port p) = In then ?shiftIn else ?shiftOut) ` set (pgraphPlaces (pgConstruct x2))"
    if not_in_1: "p \<notin> qualifyPlace ParL ` set (pgraphPlaces (pgConstruct x1))"
  proof (cases p)
    case (GroundPort qp)
    obtain n where "n \<in> set (pg_nodes (pgConstruct x2))" and "p \<in> qualifyPlace ParR ` set (nodePlaces n)"
      (* TODO why is this step so hard? *)
      using Par.prems(3)
      apply (elim pgraphPlaces_ground)
      using GroundPort apply simp
      apply (simp only: pgConstruct.simps juxtapose.simps port_graph.sel set_append)
      apply (erule UnE)
      using not_in_1
       apply (elim notE)
      using GroundPort apply (clarsimp simp add: image_Un image_Union)
       apply (metis (mono_tags, lifting) image_eqI qualifyPlace.simps(1) qualifyQPort.simps)
      using image_iff by fastforce
    then have "p \<in> qualifyPlace ParR ` set (pgraphPlaces (pgConstruct x2))"
      by fastforce
    then show ?thesis
      by (smt (z3) GroundPort image_iff qualifyPlace_shiftOpenPlace shiftOpenPlace.simps(1))
  next
    case (OpenPort p')
    then show ?thesis
      using Par.prems(3)
      apply simp
      apply (elim disjE)
           apply fastforce
          apply fastforce
      using not_in_1
         apply (metis (no_types, lifting) UnI2 image_iff list.set_map pgraphPlaces.simps qualifyPlace.simps(2) set_append)
        apply clarsimp
        apply (metis (no_types, lifting) UnCI image_eqI qualifyPlace.simps(2) shiftOpenPlace.simps(2))
      done
  qed
  then consider
    p' where "p' \<in> set (pgraphPlaces (pgConstruct x1))" and "p = qualifyPlace ParL p'"
  | p' where "p' \<in> set (pgraphPlaces (pgConstruct x2))"
    and "p = qualifyPlace ParR (?shiftIn p')" and "port.side (place_port p) = In"
  | p' where "p' \<in> set (pgraphPlaces (pgConstruct x2))"
    and "p = qualifyPlace ParR (?shiftOut p')" and "port.side (place_port p) = Out"
    by (smt (verit, ccfv_threshold) In_process_side_def Out_process_side_def image_iff process_side.exhaust)
  then show ?case
  proof cases
    case 1
    moreover have "edge_from e \<noteq> p'" if "e \<in> set (pg_edges (pgConstruct x1))" for e
    proof -
      have "qualifyEdge ParL e \<in> set (pg_edges (pgConstruct (Par x1 x2)))"
        using that by simp
      then show ?thesis
        using 1 Par.prems(4)[of "qualifyEdge ParL e"] by (meson qualifyEdge_simps(2))
    qed
    moreover have "edge_to e \<noteq> p'" if "e \<in> set (pg_edges (pgConstruct x1))" for e
    proof -
      have "qualifyEdge ParL e \<in> set (pg_edges (pgConstruct (Par x1 x2)))"
        using that by simp
      then show ?thesis
        using 1 Par.prems(5)[of "qualifyEdge ParL e"] by (meson qualifyEdge_simps(3))
    qed
    ultimately show ?thesis
      using Par.hyps(1)[where p = p'] Par.prems(1,2,6) by simp
  next
    case 2
    have "edge_from e \<noteq> p'" if "e \<in> set (pg_edges (pgConstruct x2))" for e
    proof -
      have "qualifyEdge ParR (?shift e) \<in> set (pg_edges (pgConstruct (Par x1 x2)))"
        using that by simp
      then show ?thesis
        using 2 Par.prems(4)[of "qualifyEdge ParR (?shift e)"] by (metis qualifyEdge_simps(2) shiftOpenInEdge_simps(1))
    qed
    moreover have "edge_to e \<noteq> p'" if "e \<in> set (pg_edges (pgConstruct x2))" for e
    proof -
      have "qualifyEdge ParR (?shift e) \<in> set (pg_edges (pgConstruct (Par x1 x2)))"
        using that by simp
      then have "edge_to (qualifyEdge ParR (?shift e)) \<noteq> p"
        by (rule Par.prems(5)[of "qualifyEdge ParR (?shift e)"])
      then show ?thesis
        using 2 that by clarsimp
    qed
    ultimately show ?thesis
      using Par.hyps(2)[where p = p'] 2 Par.prems(1,2,6)
      by (smt (z3) pgDefined.simps(5) not_place_ground qualifyPlace_simps(3,5)
          shiftOpenPlace_ground(1,2) shiftOpenPlace_open(2) shiftPort_simps(2,4) valid.simps(3))
  next
    case 3
    have "edge_from e \<noteq> p'" if "e \<in> set (pg_edges (pgConstruct x2))" for e
    proof -
      have "qualifyEdge ParR (?shift e) \<in> set (pg_edges (pgConstruct (Par x1 x2)))"
        using that by simp
      then have "edge_from (qualifyEdge ParR (?shift e)) \<noteq> p"
        by (rule Par.prems(4)[of "qualifyEdge ParR (?shift e)"])
      then show ?thesis
        using 3 that by clarsimp
    qed
    moreover have "edge_to e \<noteq> p'" if "e \<in> set (pg_edges (pgConstruct x2))" for e
    proof -
      have "qualifyEdge ParR (?shift e) \<in> set (pg_edges (pgConstruct (Par x1 x2)))"
        using that by simp
      then show ?thesis
        using 3 Par.prems(5)[of "qualifyEdge ParR (?shift e)"] by (metis qualifyEdge_simps(3) shiftOpenInEdge_simps(2))
    qed
    ultimately show ?thesis
      using Par.hyps(2)[where p = p'] 3 Par.prems(1,2,6)
      by (smt (z3) pgDefined.simps(5) qualifyPlace_simps(3,4,5) shiftOpenPlace_ground(2)
          shiftOpenPlace_open(1,2) shiftPort_simps(2,4) valid.simps(3))
    qed
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

  have
    " set (pgraphPlaces (pgConstruct (Duplicate x)))
    = edge_from ` set (pg_edges (pgConstruct (Duplicate x))) \<union>
      edge_to ` set (pg_edges (pgConstruct (Duplicate x)))"
    by (simp del: parallelPorts.simps add: image_comp image_Un case_prod_beta) blast
  then consider
    "p \<in> edge_from ` set (pg_edges (pgConstruct (Duplicate x)))"
  | "p \<in> edge_to ` set (pg_edges (pgConstruct (Duplicate x)))"
    using Duplicate(3) by blast
  then have False
    using Duplicate(4,5) by blast
  then show ?case ..
next
  case (Erase x)
  then show ?case by simp blast
next
  case (Represent x)
  then show ?case by simp
next
  case (Apply x1 x2a)
  then show ?case by simp
next
  case (Repeat x1 x2a)

  have
    " set (pgraphPlaces (pgConstruct (Repeat x1 x2a)))
    = edge_from ` set (pg_edges (pgConstruct (Repeat x1 x2a))) \<union>
      edge_to ` set (pg_edges (pgConstruct (Repeat x1 x2a)))"
    by (simp del: parallelPorts.simps add: image_comp image_Un case_prod_beta) blast
  then consider
    "p \<in> edge_from ` set (pg_edges (pgConstruct (Repeat x1 x2a)))"
  | "p \<in> edge_to ` set (pg_edges (pgConstruct (Repeat x1 x2a)))"
    using Repeat(3) by blast
  then have False
    using Repeat(4,5) by blast
  then show ?case ..
next
  case (Close x1 x2a)
  then show ?case by simp blast
next
  case (Once x1 x2a)

  have
    " set (pgraphPlaces (pgConstruct (Once x1 x2a)))
    = edge_from ` set (pg_edges (pgConstruct (Once x1 x2a))) \<union>
      edge_to ` set (pg_edges (pgConstruct (Once x1 x2a)))"
    by (simp del: parallelPorts.simps add: image_comp image_Un case_prod_beta) blast
  then consider
    "p \<in> edge_from ` set (pg_edges (pgConstruct (Once x1 x2a)))"
  | "p \<in> edge_to ` set (pg_edges (pgConstruct (Once x1 x2a)))"
    using Once(3) by blast
  then have False
    using Once(4,5) by blast
  then show ?case ..
next
  case (Forget x)

  show ?case
  proof (cases "x = Empty")
    case True
    then show ?thesis
      using Forget(3,6) by (simp add: parallel_parts_simps)
  next
    case False
    then have "parallel_parts x \<noteq> []"
      by (metis resource_empty resource_eq_parallel_parts)
    then have
      " set (pgraphPlaces (pgConstruct (Forget x)))
      = edge_from ` set (pg_edges (pgConstruct (Forget x))) \<union>
        edge_to ` set (pg_edges (pgConstruct (Forget x)))"
      apply (simp add: image_comp)
      apply safe
      apply (erule notE[where P = "Set.member _ _"])
      apply (rule imageI[where x = "(0, hd (parallel_parts x))"])
      apply (simp add: in_set_zip)
      by (metis add_0 hd_conv_nth length_greater_0_conv nth_upt)
    then consider
      "p \<in> edge_from ` set (pg_edges (pgConstruct (Forget x)))"
    | "p \<in> edge_to ` set (pg_edges (pgConstruct (Forget x)))"
      using Forget(3) by blast
    then have False
      using Forget(4,5) by blast
    then show ?thesis ..
  qed
qed

text\<open>
  Graphical linearity theorem for Seq-Par compositions.
  For every place of the constructed port graph, either:
  \<^item> It carries a linear resource and there is a unique edge incident on it, or
  \<^item> It carries a non-linear resource and there is no edge coming into it but an arbitrary number of
    edges coming from it, or
  \<^item> It carries a non-linear resource and there is no edge coming from it but there is a unique edge
    coming into it, or
  \<^item> It carries the anything resource and there is a unique edge coming from it but no edge coming
    into it, or
  \<^item> It carries the anything resource and there is a no edge coming from it but an arbitrary number
    of edges coming into it.
\<close>
theorem pgConstruct_linearity:
  assumes "pgDefined x"
      and "valid x"
      and "p \<in> set (pgraphPlaces (pgConstruct x))"
  obtains (Linear)
      "\<not>(\<exists>a. port.label (place_port p) = Copyable a)"
  and "\<not>(\<exists>a b. port.label (place_port p) = Repeatable a b)"
  and "port.label (place_port p) \<noteq> Anything"
  and "\<exists>!e \<in> set (pg_edges (pgConstruct x)). edge_from e = p \<or> edge_to e = p"
  | (NonLinear_Origin)
      "(\<exists>a. port.label (place_port p) = Copyable a) \<or> (\<exists>a b. port.label (place_port p) = Repeatable a b)"
  and "\<not>(\<exists>e \<in> set (pg_edges (pgConstruct x)). edge_to e = p)"
  | (NonLinear_Destin)
      "(\<exists>a. port.label (place_port p) = Copyable a) \<or> (\<exists>a b. port.label (place_port p) = Repeatable a b)"
  and "\<not>(\<exists>e \<in> set (pg_edges (pgConstruct x)). edge_from e = p)"
  and "\<exists>!e \<in> set (pg_edges (pgConstruct x)). edge_to e = p"
  | (Anything_Origin)
      "port.label (place_port p) = Anything"
  and "\<exists>!e \<in> set (pg_edges (pgConstruct x)). edge_from e = p"
  and "\<not>(\<exists>e \<in> set (pg_edges (pgConstruct x)). edge_to e = p)"
  | (Anything_Destin)
      "port.label (place_port p) = Anything"
  and "\<not>(\<exists>e \<in> set (pg_edges (pgConstruct x)). edge_from e = p)"
proof -
  interpret x: port_graph_flow "pgConstruct x"
    using assms(1,2) port_graph_flow_pgConstruct by blast

  show ?thesis
  proof (cases "port.label (place_port p) = Anything")
    case any: True
    then show ?thesis
    proof (cases "\<exists>e \<in> set (pg_edges (pgConstruct x)). edge_from e = p")
      case True
      then show ?thesis
        using assms that(4) any
        using pgConstruct_edge_copy_ground pgConstruct_edge_copy_open
        using x.edge_from_ground x.edge_from_open x.edge_to_cases x.edge_from_cases
        by (smt (verit, ccfv_threshold) Out_process_side_def edge_in_flowI(1) edge_in_flowI(2)
            in_out_distinct process_side.exhaust resource_neq(8,11))
    next
      case False
      then show ?thesis
        using that(5) any by blast
    qed
  next
    case not_any: False
    then show ?thesis
    proof (cases "(\<exists>a. port.label (place_port p) = Copyable a) \<or> (\<exists>a b. port.label (place_port p) = Repeatable a b)")
      case nonlinear: True
      then show ?thesis
      proof (cases "\<exists>e \<in> set (pg_edges (pgConstruct x)). edge_to e = p")
        case destin: True
        then show ?thesis
          using assms that(3) nonlinear not_any
          using pgConstruct_edge_noMerge_ground pgConstruct_edge_noMerge_open
          using x.edge_from_ground x.edge_from_open x.edge_to_cases
          by (smt (verit, best) edge_in_flowI(3,4) in_out_distinct process_side.exhaust)
      next
        case origin: False
        then show ?thesis
          using assms that(2) nonlinear by blast
      qed
    next
      case linear: False
      moreover have "\<exists>!e. e \<in> set (pg_edges (pgConstruct x)) \<and> (edge_from e = p \<or> edge_to e = p)"
      proof -
        obtain e where e: "e \<in> set (pg_edges (pgConstruct x))" "(edge_from e = p \<or> edge_to e = p)"
          using assms linear pgConstruct_edge_none not_any by blast
        moreover have "e' = e" if "e' \<in> set (pg_edges (pgConstruct x)) \<and> (edge_from e' = p \<or> edge_to e' = p)" for e'
        proof (cases "place_ground p")
          case True
          then show ?thesis
            using assms linear e that not_any
            using pgConstruct_edge_copy_ground pgConstruct_edge_noMerge_ground
            using x.edge_from_cases x.edge_to_cases
            by (metis (full_types) In_process_side_def edge_in_flowI(3,4) in_out_distinct process_side.exhaust x.edge_from_ground x.edge_to_ground)
        next
          case False
          then show ?thesis
            using assms linear e that not_any
            using pgConstruct_edge_copy_open pgConstruct_edge_noMerge_open
            using x.edge_from_cases x.edge_to_cases
            by (smt (verit, ccfv_SIG) edge_in_flowI(1,2) in_out_distinct process_side.exhaust)
        qed
        ultimately show ?thesis
          by blast
      qed
      ultimately show ?thesis
        using that(1) not_any by blast
    qed
  qed
qed

end