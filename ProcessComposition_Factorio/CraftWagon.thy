theory CraftWagon
  imports
    TestingPrelims
    Electricity
begin

section\<open>Crafting Cargo Wagons\<close>

text\<open>
  Process smelting iron ore into iron and steel plates, crafting iron gears and finally crafting
  one cargo wagon from per second all of them.
\<close>

context
  includes process_notation
begin

definition makeWagon
  where "makeWagon lIPlateIn lIPlateOut lSPlateIn lSPlateOut lGearIn lGearOut lWagonIn lWagonOut =
    ( perform smeltIronOre 224 lIPlateIn lIPlateOut \<parallel>
      Identity ( electric_furnace<160> at lSPlateIn \<rightarrow> lSPlateOut
               \<odot> assembling_machine_1<10> at lGearIn \<rightarrow> lGearOut
               \<odot> assembling_machine_1<2> at lWagonIn \<rightarrow> lWagonOut)) ;;
    ( liftFlowProc (splits iron_plate lIPlateOut [20, 20, 100]) \<parallel>
      Identity ( electric_furnace<160> at lSPlateIn \<rightarrow> lSPlateOut
               \<odot> assembling_machine_1<10> at lGearIn \<rightarrow> lGearOut
               \<odot> assembling_machine_1<2> at lWagonIn \<rightarrow> lWagonOut)) ;;
    ( liftFlowProc (move iron_plate 20 lIPlateOut lGearIn) \<parallel>
      liftFlowProc (move iron_plate 20 lIPlateOut lWagonIn) \<parallel>
      liftFlowProc (move iron_plate 100 lIPlateOut lSPlateIn) \<parallel>
      Identity ( electric_furnace<160> at lSPlateIn \<rightarrow> lSPlateOut
               \<odot> assembling_machine_1<10> at lGearIn \<rightarrow> lGearOut
               \<odot> assembling_machine_1<2> at lWagonIn \<rightarrow> lWagonOut)) ;;
    ( Identity (iron_plate[20] at lGearIn) \<parallel>
      Swap ( iron_plate[20] at lWagonIn
           \<odot> iron_plate[100] at lSPlateIn
           \<odot> electric_furnace<160> at lSPlateIn \<rightarrow> lSPlateOut)
           ( assembling_machine_1<10> at lGearIn \<rightarrow> lGearOut) \<parallel>
      Identity (assembling_machine_1<2> at lWagonIn \<rightarrow> lWagonOut)) ;;
    ( perform craftGear 10 lGearIn lGearOut \<parallel>
      Identity (iron_plate[20] at lWagonIn) \<parallel>
      perform smeltIronPlate 160 lSPlateIn lSPlateOut \<parallel>
      Identity (assembling_machine_1<2> at lWagonIn \<rightarrow> lWagonOut)) ;;
    ( liftFlowProc (move iron_gear 10 lGearOut lWagonIn) \<parallel>
      Identity (iron_plate[20] at lWagonIn) \<parallel>
      liftFlowProc (move steel_plate 20 lSPlateOut lWagonIn) \<parallel>
      Identity (assembling_machine_1<2> at lWagonIn \<rightarrow> lWagonOut)) ;;
    ( perform craftWagon 2 lWagonIn lWagonOut)"

end

lemma makeWagon:
  shows "valid (makeWagon lII lIO lSI lSO lGI lGO lWI lWO)"
    and " input (makeWagon lII lIO lSI lSO lGI lGO lWI lWO)
        =   iron_ore[140] at lII
          \<odot> electric_furnace<224> at lII \<rightarrow> lIO
          \<odot> electric_furnace<160> at lSI \<rightarrow> lSO
          \<odot> assembling_machine_1<10> at lGI \<rightarrow> lGO
          \<odot> assembling_machine_1<2> at lWI \<rightarrow> lWO"
    and "output (makeWagon lII lIO lSI lSO lGI lGO lWI lWO) = cargo_wagon[1] at lWO"
    and "electricity (makeWagon lII lIO lSI lSO lGI lGO lWI lWO) = 72354 * 10^3"
  by (simp_all add: makeWagon_def TestingPrelims.defs resource_par_res resource_parallel_res)

text\<open>
  Composition validity would ensure that we account for any leftover from processing not dividing
  perfectly into the demand.
  But in this case there is no need, as the ratios work out perfectly balanced.
\<close>

end