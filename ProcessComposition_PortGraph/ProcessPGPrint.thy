theory ProcessPGPrint
  imports
    ProcessPortGraph
    PortGraph_Export.ELKJson
    PortGraph_Export.PetriNetDot
begin

section\<open>Process Port Graph Printing\<close>

primrec processInnerToString :: "process_inner \<Rightarrow> String.literal"
  where
    "processInnerToString SeqL = STR ''SeqL''"
  | "processInnerToString SeqR = STR ''SeqR''"
  | "processInnerToString ParL = STR ''ParL''"
  | "processInnerToString ParR = STR ''ParR''"
  | "processInnerToString OptL = STR ''OptL''"
  | "processInnerToString OptR = STR ''OptR''"
  | "processInnerToString Rep = STR ''Rep''"

primrec processPathToString :: "process_inner list \<Rightarrow> String.literal"
  where
    "processPathToString [] = STR ''''"
  | "processPathToString (x#xs) = processInnerToString x + processPathToString xs"

primrec processLabelToString :: "(String.literal, 'm) node_content \<Rightarrow> String.literal"
  where
    "processLabelToString (NodePrimitive l m) = l"

fun intercalate :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "intercalate a [] = []"
  | "intercalate a [x] = [x]"
  | "intercalate a (x#xs) = x # a # intercalate a xs"

value "sum_list (intercalate STR '', '' [STR ''A'', STR ''B'', STR ''C'', STR ''D''])"
value "sum_list (intercalate STR '', '' [STR ''A''])"
value "sum_list (intercalate STR '', '' [])"

primrec res_termToString :: "(String.literal, String.literal) res_term \<Rightarrow> String.literal"
  where
    "res_termToString res_term.Empty = STR ''Empty''"
  | "res_termToString res_term.Anything = STR ''Anything''"
  | "res_termToString (res_term.Res a) = STR ''Res '' + a"
  | "res_termToString (res_term.Copyable x) = STR ''Copyable '' + x"
  | "res_termToString (res_term.Parallel xs) = STR ''Parallel ['' + sum_list (intercalate STR '', '' (map res_termToString xs)) + STR '']''"
  | "res_termToString (res_term.NonD x y) = STR ''NonD ('' + res_termToString x + STR '', '' + res_termToString y + STR '')''"
  | "res_termToString (res_term.Executable x y) = STR ''Executable ('' + res_termToString x + STR '', '' + res_termToString y + STR '')''"
  | "res_termToString (res_term.Repeatable x y) = STR ''Repeatable ('' + res_termToString x + STR '', '' + res_termToString y + STR '')''"

definition resourceToString :: "(String.literal, String.literal) resource \<Rightarrow> String.literal"
  where "resourceToString x = res_termToString (of_resource x)"

lemmas [code] =
  portGraphELK.portGraphToJSON_def
  portGraphELK.nodeToJSON_def
  portGraphELK.groundPortToJSON_def
  portGraphELK.edgeToJSON_def
  portGraphELK.groundPlaceToID_def
  portGraphELK.openPlaceToID_def
  portGraphELK.placeToID_def
  portGraphELK.openPortToJSON_def
  portGraphPN.portGraphToPN_def
  portGraphPN.nodeToPN_def
  portGraphPN.edgeToPN_def
  portGraphPN.placeToID.simps
  portGraphPN.groundPlaceToNodeID.simps

fun processToELK :: "(String.literal, String.literal, String.literal, unit) process \<Rightarrow> (String.literal, int) json"
  where "processToELK x = portGraphELK.portGraphToJSON processPathToString processLabelToString sideInOutToELK resourceToString [] (pgConstruct x)"

primrec processSideToString :: "process_side \<Rightarrow> String.literal"
  where
    "processSideToString process_side.In = STR ''In''"
  | "processSideToString process_side.Out = STR ''Out''"

definition "test2 \<equiv> portGraphPN.portGraphToPN processPathToString processLabelToString resourceToString processSideToString [] (pgConstruct (
  seq_process_list [
    Primitive (Res STR ''A'') (Res STR ''B'' \<odot> Res STR ''C'') STR ''P'' ()
  , par_process_list [
      Primitive (Res STR ''B'') (Res STR ''D'') STR ''R'' ()
    , Primitive (Res STR ''C'') (Res STR ''E'') STR ''S'' ()
    ]
  , par_process_list [
      Primitive (Res STR ''D'') (Res STR ''F'') STR ''T'' ()
    , Primitive (Res STR ''E'') (Res STR ''G'') STR ''U'' ()
    ]
  ]
))"

(* Isabelle's string literal evaluation does not like escaped quotes and wants to print them as bytes *)
definition carrier :: "(String.literal, int) json" where "carrier \<equiv> STRING test2"

setup\<open>fn t =>
let
  val state = Toplevel.make_state (SOME t)
  val ctxt = Toplevel.context_of state;
  val term = Syntax.read_term ctxt "carrier";
  val term' = Value_Command.value_select "" ctxt term;
  val j = Pretty.str (Nano_Json_Serializer.serialize_term_pretty term')
  val _ = Pretty.writeln j
in t end
\<close>

end
