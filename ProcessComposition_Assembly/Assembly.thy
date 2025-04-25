theory Assembly
  imports
    ProcessComposition.Process
begin

section\<open>Assembly Process\<close>

text\<open>
  The assembly process follows an order, representing e.g. data from an Enterprise Resource Planning
  system, which is structured as a tree of assemblies, each one applying a list of operations to a
  production lot.
  This represents a generic way of modelling manufacturing e.g. in a metalworking shop.

  Machines used to perform the operations are taken from an unmodelled context.
  If multiple of these processes were to be put into the same (real or simulated) environment, this
  part could be a source of waiting.
  However, it should not be a source of deadlock, because no operation holds a machine while waiting
  for another.

  We define the relevant composition as a function of the order data structure, which allows us to
  handle any number of operations at any level of the assembly hierarchy, with the hierarchy having
  any (finite) depth and width.

  We prove that the composition is valid for all orders.
\<close>

(* Possible extensions notes: *)
(* TODO
  A parameter on Machine could be used to ensure we don't reserve and free a machine without
  actually using it, which is not vital but could be seen as reducing unnecessary allocation of
  machines and thus some form of waste.
 *)
(* TODO
  A lot could carry the history of operations done on it, so that it actually changes through the
  operations.
  This seems overly complex for the present example, but would not be hard to do in practice.
*)
(* TODO
  In an implementation, the operation and machine should probably have further parameters to
  represent some notion of the type of machine needed.
  The present example assumes a simplified single pool of machines.
*)
(* TODO
  We could also model a notion of location, adding it to each lot and machine as well as adding
  movement actions for lots.
  This would however mean that the reserve action would need to be able to predict the location of
  the machine it gets from the pool.
  It depends on the domain whether this is a reasonable thing to assume about the domain (e.g. all
  machines for a particular type of operation could be at one location).
*)

subsection\<open>Order Data\<close>

text\<open>An operation is defined by a string label\<close>
datatype operation = Op (op_label: String.literal)

text\<open>An order has a string identifier, any number of suborders and any number of operations\<close>
datatype order = Order (orderID: String.literal) (suborders: "order list") (operations: "operation list")

text\<open>Order depth can be determined by traversing the tree, taking maximum child depth at every node\<close>
fun order_depth :: "order \<Rightarrow> nat"
  where
    "order_depth (Order _ [] _) = 0"
  | "order_depth (Order i (x#xs) y) = max (order_depth x) (order_depth (Order i xs y)) + 1"

text\<open>Every order is deeper than its suborders\<close>
lemma suborder_depth_less [simp]:
  "x \<in> set (suborders y) \<Longrightarrow> order_depth x < order_depth y"
proof (induct rule: order_depth.induct)
  case (1 uu uv)
  then show ?case by simp
next
  case (2 i x xs y)
  then show ?case by fastforce
qed

subsection\<open>Resources\<close>

text\<open>Linear resources are the production lots and the machines\<close>
datatype res = Lot | Machine

subsection\<open>Operations at Machines\<close>

subsubsection\<open>Primitive Actions\<close>

text\<open>Reserve a machine from some unmodeled pool\<close>
definition reserve :: "(res, unit, String.literal, unit) process"
  where [simp]: "reserve = Primitive Empty (Res Machine) STR ''Reserve a machine'' ()"

text\<open>Free a machine\<close>
definition free :: "(res, unit, String.literal, unit) process"
  where [simp]: "free \<equiv> Primitive (Res Machine) Empty STR ''Free a machine'' ()"

text\<open>Perform an operation at a machine\<close>
definition perform :: "operation \<Rightarrow> (res, unit, String.literal, unit) process"
  where [simp]: "perform op =
    Primitive (Res Machine \<odot> Res Lot)
              (Res Machine \<odot> Res Lot)
              (STR ''Operation: '' + op_label op)
              ()"

text\<open>
  We separate reserving a machine and performing the operation so that, if we were to monitor an
  implementation of this process (real or simulated) we could distinguish the delay introduced by
  waiting for a machine to be available and the one introduced by actually performing the operation.
\<close>

subsubsection\<open>Helper Compositions\<close>

text\<open>Perform a single operation, reserving and freeing a machine\<close>
definition op :: "operation \<Rightarrow> (res, unit, String.literal, unit) process"
  where [simp]: "op x =
  seq_process_list [
    Par reserve (Identity (Res Lot))
  , perform x
  , Par free (Identity (Res Lot))
  ]"

lemma op [simp]:
  "input (op x) = Res Lot"
  "output (op x) = Res Lot"
  "valid (op x)"
  by simp_all

text\<open>Chain that to perform a list of operations\<close>
fun ops :: "operation list \<Rightarrow> (res, unit, String.literal, unit) process"
  where
    "ops [] = Identity (Res Lot)"
  | "ops (x#xs) = (if xs = [] then op x else Seq (op x) (ops xs))"

lemma ops [simp]:
  "input (ops xs) = Res Lot"
  "output (ops xs) = Res Lot"
  "valid (ops xs)"
  by (induct xs) simp_all

subsection\<open>Assemble Primitive Action\<close>

text\<open>
  Assemble the results of an order's suborders into one lot.
  When there are no subassemblies, this process still occurs but with no inputs.
  This may represent collecting raw resources (which are not modelled) into a lot.
\<close>
definition assemble :: "order \<Rightarrow> (res, unit, String.literal, unit) process"
  where [simp]: "assemble x =
    Primitive (Parallel (replicate (length (suborders x)) (Res Lot)))
              (Res Lot)
              (STR ''Assemble '' + orderID x)
              ()"

subsection\<open>Assembly Composition\<close>

text\<open>
  Build the assembly process for an order, by first recursing into suborders, then assembling their
  results and finally performing the list of operations.
\<close>
function assm :: "order \<Rightarrow> (res, unit, String.literal, unit) process"
  where "assm x =
  Seq ( par_process_list (map assm (suborders x)))
      ( Seq (assemble x)
            (ops (operations x)))"
  by simp_all

text\<open>This definition terminates due to decreasing depth of the order\<close>
termination assm
  by (relation "Wellfounded.measure order_depth", auto)

lemma assm [simp]:
  "input (assm order) = Empty"
  "output (assm order) = Res Lot"
  "valid (assm order)"
proof (induct order)
  case (Order i s ope)
  {
    case 1
    then show ?case
      using Order by (induct s) simp_all
  next
    case 2
    then show ?case
      by simp
  next
    case 3
    then show ?case
      using Order by (induct s) simp_all
  }
qed

end
