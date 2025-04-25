theory ProcessesModuloPGs
  imports
    ProcessCatSubtype
begin

section\<open>Processes Modulo Port Graphs\<close>

text\<open>
  Process compositions as they are do not form a category, since we have syntactically distinct
  entitites that laws of composition would require to be equal.
  For this purpose we form a suitable quotient of process compositions, equating the relevant forms.
\<close>

subsection\<open>Process Equivalence Relation\<close>

text\<open>
  The equivalence relation we will use relates two valid process compositions if:
  \<^item> They have the same input resource, and
  \<^item> They have the same output resource, and
  \<^item> They yield equivalent port graphs.

  (It relates all invalid compositions, lumping them into one equivalence class.)
\<close>
definition process_equiv :: "('a, 'b, 'l, 'm) proc \<Rightarrow> ('a, 'b, 'l, 'm) proc \<Rightarrow> bool"
  where "process_equiv x y =
  ( if valid x
      then valid y \<and> input x = input y \<and> output x = output y \<and> pgConstruct x \<approx> pgConstruct y
      else \<not> valid y)"

text\<open>Port graph construction definition should at this point only be unfolded on request\<close>
lemmas [simp del] = pgConstruct.simps

text\<open>It is an equivalence relation\<close>
lemma process_equiv_equivp:
  "equivp process_equiv"
proof (intro equivpI)
  show "reflp process_equiv"
    by (simp add: process_equiv_def reflpI)
  show "symp process_equiv"
    using process_equiv_def pgEquiv_sym sympI by (metis (mono_tags))
  show "transp process_equiv"
    using process_equiv_def pgEquiv_trans transpI by (metis (mono_tags))
qed

subsection\<open>Quotient\<close>

text\<open>Process compositions have the functorial structure used by quotient types\<close>
functor map_process
proof
  fix m :: "'x \<Rightarrow> 't"
  and l :: "'w \<Rightarrow> 's"
  and k :: "'v \<Rightarrow> 'r"
  and j :: "'u \<Rightarrow> 'q"
  and i :: "'t \<Rightarrow> 'p"
  and h :: "'s \<Rightarrow> 'o"
  and g :: "'r \<Rightarrow> 'n"
  and f :: "'q \<Rightarrow> 'm"
  and x :: "('u, 'v, 'w, 'x) proc"
  show
    " (map_process f g h i \<circ> map_process j k l m) x
    = map_process (f \<circ> j) (g \<circ> k) (h \<circ> l) (i \<circ> m) x"
    by transfer (simp add: process.map_comp)
next
  have "map_process id id id id x = id x" for x :: "('m, 'n, 'o, 'p) proc"
    by transfer (simp add: process.map_id0)
  then show "map_process id id id id = id" ..
qed

text\<open>Quotient the subtype of process compositions with port graphs by the equivalence relation\<close>
quotient_type ('a, 'b, 'l, 'm) eq_process = "('a, 'b, 'l, 'm) proc" / process_equiv
  by (rule process_equiv_equivp)

text\<open>Lift again all operations from the subtype to the quotient type\<close>
lift_definition
  Primitive :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Primitive .
lift_definition
  Identity :: "('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Identity .
lift_definition
  Swap :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Swap .
lift_definition
  Duplicate :: "'b \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Duplicate .
lift_definition
  Erase :: "'b \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Erase .
lift_definition
  Repeat :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Repeat .
lift_definition
  Once :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Once .
lift_definition
  Close :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Close .
lift_definition
  Forget :: "('a, 'b) resource \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Forget .

lift_definition
  Seq :: "('a, 'b, 'l, 'm) eq_process \<Rightarrow> ('a, 'b, 'l, 'm) eq_process \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Seq
  unfolding process_equiv_def
  apply transfer
  apply (case_tac "Process.valid proc1" ; clarsimp)
  apply (case_tac "Process.valid proc3" ; clarsimp)
  apply (simp add: pgConstruct.simps del: seqPortGraphs.simps)
  using seqPortGraphs_resp port_graph_flow_pgConstruct port_graph_flow_qualifyPortGraph pgEquiv_qualifyPortGraph qualifyPortGraph_apart
  by (smt (verit, ccfv_threshold) pgEquiv_sym pgEquiv_trans port_graph_flow.axioms(1) process_inner.distinct)
lift_definition
  Par :: "('a, 'b, 'l, 'm) eq_process \<Rightarrow> ('a, 'b, 'l, 'm) eq_process \<Rightarrow> ('a, 'b, 'l, 'm) eq_process"
  is ProcessCatSubtype.Par
  unfolding process_equiv_def
  apply transfer
  apply (case_tac "Process.valid proc1" ; clarsimp)
  apply (case_tac "Process.valid proc3" ; clarsimp)
  apply (simp add: pgConstruct.simps del: juxtapose.simps)
  using juxtapose_resp port_graph_flow_pgConstruct port_graph_flow_qualifyPortGraph pgEquiv_qualifyPortGraph qualifyPortGraph_apart
  by (smt (verit, ccfv_threshold) pgEquiv_sym pgEquiv_trans port_graph_flow.axioms(1) process_inner.distinct)

lift_definition
  valid :: "('a, 'b, 'l, 'm) eq_process \<Rightarrow> bool"
  is ProcessCatSubtype.valid
  by (metis process_equiv_def)

lift_definition
  map_process :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> ('a, 'c, 'e, 'g) proc \<Rightarrow> ('b, 'd, 'f, 'h) proc"
  is Process.map_process
  by simp

text\<open>
  In the case of input and output we need a fallback for invalid compositions so that they respect
  the equivalence relation.
  That is, all elements of each equivalence class (especially the class of all invalid compositions)
  have equal input and output.
\<close>
lift_definition
  input :: "('a, 'b, 'l, 'm) eq_process \<Rightarrow> ('a, 'b) resource"
  is "\<lambda>p. if ProcessCatSubtype.valid p then ProcessCatSubtype.input p else undefined"
  by (simp add: process_equiv_def)
lift_definition
  "output" :: "('a, 'b, 'l, 'm) eq_process \<Rightarrow> ('a, 'b) resource"
  is "\<lambda>p. if ProcessCatSubtype.valid p then ProcessCatSubtype.output p else undefined"
  by (simp add: process_equiv_def)

text\<open>At this point, transfer between resources and resource terms gets in the way more than it helps\<close>
lifting_forget resource.lifting

text\<open>Lift some simpsets\<close>
lemma input_simps [simp]:
  "input (Primitive ins outs l m) = ins"
  "input (Identity a) = a"
  "input (Swap a b) = a \<odot> b"
  "valid (Seq p q) \<Longrightarrow> input (Seq p q) = input p"
  "valid (Par p q) \<Longrightarrow> input (Par p q) = input p \<odot> input q"
  "input (Duplicate a) = Copyable a"
  "input (Erase a) = Copyable a"
  "input (Repeat a b) = Repeatable a b"
  "input (Close a b) = Repeatable a b"
  "input (Once a b) = Repeatable a b"
  "input (Forget a) = a"
  by (transfer, transfer, simp)+

lemma output_simps [simp]:
  "output (Primitive ins outs l m) = outs"
  "output (Identity a) = a"
  "output (Swap a b) = b \<odot> a"
  "valid (Seq p q) \<Longrightarrow> output (Seq p q) = output q"
  "valid (Par p q) \<Longrightarrow> output (Par p q) = output p \<odot> output q"
  "output (Duplicate a) = Copyable a \<odot> Copyable a"
  "output (Erase a) = Empty"
  "output (Close a b) = Empty"
  "output (Once a b) = Executable a b"
  "output (Forget a) = Anything"
  by (transfer, transfer, simp)+

lemma valid_simps [simp]:
  "valid (Primitive ins outs l m) = True"
  "valid (Identity a) = True"
  "valid (Swap a b) = True"
  "valid (Seq p q) = (output p = input q \<and> valid p \<and> valid q)"
  "valid (Par p q) = (valid p \<and> valid q)"
  "valid (Duplicate a) = True"
  "valid (Erase a) = True"
  "valid (Repeat a b) = True"
  "valid (Close a b) = True"
  "valid (Once a b) = True"
  "valid (Forget a) = True"
  by (transfer, transfer, simp)+

end