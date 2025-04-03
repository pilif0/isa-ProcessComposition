theory Manufacturing
  imports
    Item
    Machine
begin

section\<open>Manufacturing Action\<close>

text\<open>
  Recipes are defined by:
  \<^item> Input item-count pairs,
  \<^item> Output item-count pairs,
  \<^item> Time taken in seconds,
  \<^item> Machine used, and
  \<^item> String label.
\<close>
datatype recipe =
  Recipe (recIn: "(item \<times> nat) list") (recOut: "(item \<times> nat) list") (recTime: rat)
         (recMach: machine) (recLab: String.literal)

text\<open>
  Construct an item flow given:
  \<^item> Some recipe's time requirement,
  \<^item> Location of the flow,
  \<^item> Number of machines performing that recipe in parallel,
  \<^item> Processing speed of each of the machines, and
  \<^item> Pair of item and its count.

  The final argument is given as a pair to allow for mapping over a list of pairs given as part of
  the recipe to easily get flows for all its inputs/outputs.
\<close>
fun stacksPerTimeAtSpeed :: "rat \<Rightarrow> loc \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> item \<times> nat \<Rightarrow> flow"
  where "stacksPerTimeAtSpeed t l n s (u,v) = Flow u (s * of_nat (n*v) / t) l"

text\<open>Manufacturing action metadata\<close>
datatype manu_meta = Perform recipe nat loc loc

text\<open>
  There is an action performing some number of instances of a recipe in parallel on a block of
  machines.
  Note that the block of machines is consumed by the action, since those machines remain perpetually
  occupied with performing this recipe.
\<close>
fun perform :: "recipe \<Rightarrow> nat \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> (flow + mach_block, unit, String.literal, flow_meta + manu_meta) process"
  where "perform r n l1 l2 =
  ( Primitive
      ( Parallel (map (Res \<circ> Inl \<circ> stacksPerTimeAtSpeed (recTime r) l1 n (machineSpeed (recMach r))) (recIn r))
        \<odot> Res (Inr (MachBlock (recMach r) n l1 l2)))
      ( Parallel (map (Res \<circ> Inl \<circ> stacksPerTimeAtSpeed (recTime r) l2 n (machineSpeed (recMach r))) (recOut r)))
      (recLab r)
      (Inr (Perform r n l1 l2)))"

text\<open>Lift any process on just item flows to manufacturing\<close>
abbreviation "liftFlowProc \<equiv> map_process Inl id id Inl"

end