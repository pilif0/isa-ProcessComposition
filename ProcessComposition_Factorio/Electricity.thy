theory Electricity
  imports
    Manufacturing
begin

section\<open>Electricity Usage\<close>

text\<open>Sum up linear atoms in parallel resource terms\<close>
primrec sum_parallel_t :: "('a :: monoid_add, 'b) res_term \<Rightarrow> 'a"
  where
    "sum_parallel_t ResTerm.Empty = 0"
  | "sum_parallel_t ResTerm.Anything = undefined"
  | "sum_parallel_t (ResTerm.Res u) = u"
  | "sum_parallel_t (ResTerm.Copyable a) = undefined"
  | "sum_parallel_t (ResTerm.Parallel xs) = sum_list (map sum_parallel_t xs)"
  | "sum_parallel_t (ResTerm.NonD a b) = undefined"
  | "sum_parallel_t (ResTerm.Executable a b) = undefined"
  | "sum_parallel_t (ResTerm.Repeatable a b) = undefined"

text\<open>Lift summing up of parallel atoms from terms to resources\<close>
lift_definition sum_parallel :: "('a :: monoid_add, 'b) resource \<Rightarrow> 'a" is sum_parallel_t
proof -
  fix x y :: "('a, 'b) res_term"
  show "x \<sim> y \<Longrightarrow> sum_parallel_t x = sum_parallel_t y"
  proof (induct rule: res_term_equiv.induct ; simp)
    case (parallel xs ys)
    then show "sum_list (map sum_parallel_t xs) = sum_list (map sum_parallel_t ys)"
    proof (induct xs arbitrary: ys rule: list.induct)
      case Nil
      then show ?case by simp
    next
      case (Cons x1 x2)
      then show ?case
        by (smt (verit) list.simps(9) list_all2_Cons1 sum_list.Cons)
    qed
  qed
qed

text\<open>Prove simplification rules for the lifted summing up of parallel atoms\<close>
lemma sum_parallel_simps [simp]:
  "sum_parallel Empty = 0"
  "sum_parallel Anything = undefined"
  "sum_parallel (Res u) = u"
  "sum_parallel (Copyable a) = undefined"
  "sum_parallel (Parallel xs) = sum_list (map sum_parallel xs)"
  "sum_parallel (NonD a b) = undefined"
  "sum_parallel (Executable a b) = undefined"
  by (transfer, simp)+

lemma sum_parallel_par [simp]:
  "sum_parallel (a \<odot> b) = sum_parallel a + sum_parallel b"
  by (simp add: resource_par_def)

text\<open>
  Electricity usage of a resource atom in this domain is:
  \<^item> Zero for an item flow, and
  \<^item> Drain plus consumption for each machine in a machine block.
\<close>
fun elec_res :: "flow + mach_block \<Rightarrow> nat"
  where
    "elec_res (Inl _) = 0"
  | "elec_res (Inr (MachBlock m n _ _)) = n * (machineDrain m + machineConsu m)"

text\<open>Electricity usage of a process is the total usage of machine blocks it consumes\<close>
fun electricity :: "(flow + mach_block, 'b, 'l, 'm) process \<Rightarrow> nat"
  where "electricity p =
    sum_parallel (map_resource elec_res id (input p)) -
    sum_parallel (map_resource elec_res id (output p))"

end