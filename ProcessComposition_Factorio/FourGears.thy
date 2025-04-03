theory FourGears
  imports
    TestingPrelims
    Electricity
begin

section\<open>Four Iron Gears\<close>

text\<open>Process smelting iron ore into plates and crafting four iron gears from them per second\<close>

context
  includes process_notation
begin

definition "fourGears lIPlateIn lIPlateOut lGearIn lGearOut =
    ( perform smeltIronOre 13 lIPlateIn lIPlateOut \<parallel>
      Identity (assembling_machine_1<4> at lGearIn \<rightarrow> lGearOut)) ;;
    ( liftFlowProc (split iron_plate lIPlateOut 0.125 8) \<parallel>
      Identity (assembling_machine_1<4> at lGearIn \<rightarrow> lGearOut)) ;;
    ( Identity (iron_plate[0.125] at lIPlateOut) \<parallel>
      liftFlowProc (move iron_plate 8 lIPlateOut lGearIn) \<parallel>
      Identity (assembling_machine_1<4> at lGearIn \<rightarrow> lGearOut)) ;;
    ( Identity (iron_plate[0.125] at lIPlateOut) \<parallel>
      perform craftGear 4 lGearIn lGearOut)"

end

lemma fourGears:
  shows "valid (fourGears lPI lPO lGI lGO)"
    and " input (fourGears lPI lPO lGI lGO)
        =   iron_ore[8.125] at lPI
          \<odot> electric_furnace<13> at lPI \<rightarrow> lPO
          \<odot> assembling_machine_1<4> at lGI \<rightarrow> lGO"
    and " output (fourGears lPI lPO lGI lGO)
        =   iron_plate[0.125] at lPO
          \<odot> iron_gear[4] at lGO"
    and "electricity (fourGears lPI lPO lGI lGO) = 2728 * 10^3"
  by (simp_all add: fourGears_def TestingPrelims.defs)

end