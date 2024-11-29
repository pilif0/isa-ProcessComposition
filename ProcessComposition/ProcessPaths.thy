theory ProcessPaths
  imports Process
begin

section\<open>Process Paths\<close>

text\<open>
  Because process compositions are represented by trees, we can use paths to uniquely identify
  specific subtrees and, by extension, leaves.
  We use these paths as unique identifiers in visualisations and, in conjunction with input/output
  side and index, to uniquely identify occurrences of resources within a process.
\<close>

text\<open>
  First, we define path elements as the possible children of composition actions.
  Because those actions are at most binary, we only strictly need two elements.
  However, to make the paths more readable with respect to a composition at hand, we define a path
  element for each pair of composition action and child.
  Paths in process composition trees are then lists of these elements.
\<close>
datatype process_inner = SeqL | SeqR | ParL | ParR | OptL | OptR | Rep

subsection\<open>Subprocess Retrieval\<close>

text\<open>
  We can attempt to get the relevant subprocess given a path element, with the output being optional
  as no such subprocess may exist (e.g.\ if the process is a single action).
\<close>
primrec subprocessStep
    :: "process_inner \<Rightarrow> ('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l, 'm) process option"
  where
    "subprocessStep SeqL p = (case p of Seq x y \<Rightarrow> Some x | _ \<Rightarrow> None)"
  | "subprocessStep SeqR p = (case p of Seq x y \<Rightarrow> Some y | _ \<Rightarrow> None)"
  | "subprocessStep ParL p = (case p of Par x y \<Rightarrow> Some x | _ \<Rightarrow> None)"
  | "subprocessStep ParR p = (case p of Par x y \<Rightarrow> Some y | _ \<Rightarrow> None)"
  | "subprocessStep OptL p = (case p of Opt x y \<Rightarrow> Some x | _ \<Rightarrow> None)"
  | "subprocessStep OptR p = (case p of Opt x y \<Rightarrow> Some y | _ \<Rightarrow> None)"
  | "subprocessStep Rep p = (case p of Represent x \<Rightarrow> Some x | _ \<Rightarrow> None)"

text\<open>With option's monadic bind, we can extend this to a path\<close>
fun subprocess
    :: "process_inner list \<Rightarrow> ('a, 'b, 'l, 'm) process \<Rightarrow> ('a, 'b, 'l, 'm) process option"
  where "subprocess p x = foldl (\<lambda>a b. Option.bind a (subprocessStep b)) (Some x) p"

lemma subprocess_simps:
  "subprocess [] x = Some x"
  "subprocess (SeqL # ps) (Seq x y) = subprocess ps x"
  "subprocess (SeqR # ps) (Seq x y) = subprocess ps y"
  "subprocess (ParL # ps) (Par x y) = subprocess ps x"
  "subprocess (ParR # ps) (Par x y) = subprocess ps y"
  "subprocess (OptL # ps) (Opt x y) = subprocess ps x"
  "subprocess (OptR # ps) (Opt x y) = subprocess ps y"
  "subprocess (Rep # ps) (Represent x) = subprocess ps x"
  by simp_all

subsection\<open>Named Primitive Actions\<close>

text\<open>
  With this we can get the list of primitive actions along with their unique identifiers within the
  original composition
\<close>
primrec namedPrimitives
    :: "('a, 'b, 'l, 'm) process
    \<Rightarrow> (process_inner list \<times> ('a, 'b) resource \<times> ('a, 'b) resource \<times> 'l \<times> 'm) list"
  where
    "namedPrimitives (Primitive ins outs l m) = [([], ins, outs, l, m)]"
  | "namedPrimitives (Identity a) = []"
  | "namedPrimitives (Swap a b) = []"
  | "namedPrimitives (Seq p q) =
      map (\<lambda>(n, ins, outs, l, m). (SeqL # n, ins, outs, l, m)) (namedPrimitives p)
    @ map (\<lambda>(n, ins, outs, l, m). (SeqR # n, ins, outs, l, m)) (namedPrimitives q)"
  | "namedPrimitives (Par p q) =
      map (\<lambda>(n, ins, outs, l, m). (ParL # n, ins, outs, l, m)) (namedPrimitives p)
    @ map (\<lambda>(n, ins, outs, l, m). (ParR # n, ins, outs, l, m)) (namedPrimitives q)"
  | "namedPrimitives (Opt p q) =
      map (\<lambda>(n, ins, outs, l, m). (OptL # n, ins, outs, l, m)) (namedPrimitives p)
    @ map (\<lambda>(n, ins, outs, l, m). (OptR # n, ins, outs, l, m)) (namedPrimitives q)"
  | "namedPrimitives (InjectL a b) = []"
  | "namedPrimitives (InjectR a b) = []"
  | "namedPrimitives (OptDistrIn a b c) = []"
  | "namedPrimitives (OptDistrOut a b c) = []"
  | "namedPrimitives (Duplicate a) = []"
  | "namedPrimitives (Erase a) = []"
  | "namedPrimitives (Represent p) =
      map (\<lambda>(n, ins, outs, l, m). (Rep # n, ins, outs, l, m)) (namedPrimitives p)"
  | "namedPrimitives (Apply a b) = []"
  | "namedPrimitives (Repeat a b) = []"
  | "namedPrimitives (Close a b) = []"
  | "namedPrimitives (Once a b) = []"
  | "namedPrimitives (Forget a) = []"

text\<open>This expands on the information that @{const primitives} can provide\<close>
lemma namedPrimitives_contains_primitives:
  "map snd (namedPrimitives x) = primitives x"
  by (induct x) (simp_all add: comp_def case_prod_beta)

end
