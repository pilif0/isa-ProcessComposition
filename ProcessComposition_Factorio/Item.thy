theory Item
  imports
    Location
    HOL.Rat
    ProcessComposition.Process
begin

section\<open>Item Flows\<close>

text\<open>Items are string labels\<close>
datatype item = Item (itemLabel: String.literal)

text\<open>Item flows are items at some rate (per second) at a location\<close>
datatype flow = Flow (flowItem: item) (flowRate: rat) (flowLoc: loc)

(* Note: convenient notation for flows is introduced in TestingPrelims.thy *)

section\<open>Logistics Actions\<close>

text\<open>Metadata of logistics actions\<close>
datatype flow_meta =
  Merge item loc rat rat
  | Unit item loc
  | Split item loc rat rat
  | Counit item loc
  | Move item rat loc loc

text\<open>There is an action to move any flow from one location to any other\<close>
definition move :: "item \<Rightarrow> rat \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> (flow, unit, String.literal, flow_meta) process"
  where "move i r l k =
  Primitive (Res (Flow i r l)) (Res (Flow i r k)) STR ''Move flow'' (Move i r l k)"

text\<open>There is an action to merge two flows into one, and an action creating a zero-rate flow\<close>
definition merge :: "item \<Rightarrow> loc \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> (flow, unit, String.literal, flow_meta) process"
  where "merge i l r s =
  Primitive (Res (Flow i r l) \<odot> Res (Flow i s l)) (Res (Flow i (r+s) l))
            STR ''Merge flows'' (Merge i l r s)"
definition unit :: "item \<Rightarrow> loc \<Rightarrow> (flow, unit, String.literal, flow_meta) process"
  where "unit i l =
  Primitive Empty (Res (Flow i 0 l)) STR ''Create zero flow'' (Unit i l)"

text\<open>There is an action to split one flow into two, and an action discarding a zero-rate flow\<close>
definition split :: "item \<Rightarrow> loc \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> (flow, unit, String.literal, flow_meta) process"
  where "split i l r s =
  Primitive (Res (Flow i (r+s) l)) (Res (Flow i r l) \<odot> Res (Flow i s l))
            STR ''Split flow'' (Split i l r s)"
definition counit :: "item \<Rightarrow> loc \<Rightarrow> (flow, unit, String.literal, flow_meta) process"
  where "counit i l =
  Primitive (Res (Flow i 0 l)) Empty STR ''Discard zero flow'' (Counit i l)"

lemmas [simp] = move_def merge_def unit_def split_def counit_def

subsection\<open>Helper Functions\<close>

text\<open>Compose splits from a single flow into multiple according to a list of desired output rates\<close>
fun splits :: "item \<Rightarrow> loc \<Rightarrow> rat list \<Rightarrow> (flow, unit, String.literal, flow_meta) process"
  where
    "splits i l [] = Identity (Res (Flow i 0 l))"
  | "splits i l [n] = Identity (Res (Flow i n l))"
  | "splits i l [m,n] = split i l m n"
  | "splits i l (a#b#c#ns) =
      Seq (split i l a (sum_list (b#c#ns)))
          ( Par (Identity (Res (Flow i a l)))
                (splits i l (b#c#ns)))"

end