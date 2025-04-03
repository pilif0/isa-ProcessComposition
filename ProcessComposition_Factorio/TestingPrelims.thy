theory TestingPrelims
  imports
    Manufacturing
begin

section\<open>Testing Preliminaries\<close>

definition "iron_plate = Item STR ''Iron Plate''"
definition "steel_plate = Item STR ''Steel Plate''"
definition "iron_gear = Item STR ''Iron Gear''"
definition "iron_ore = Item STR ''Iron Ore''"
definition "cargo_wagon = Item STR ''Cargo Wagon''"

definition "electric_furnace = Machine STR ''Electric Furnace'' 2 6000 180000"
definition "assembling_machine_1 = Machine STR ''Assembling Machine 1'' 0.5 2500 75000"

definition "smeltIronOre = Recipe
  [(iron_ore, 1)]
  [(iron_plate, 1)]
  3.2 electric_furnace STR ''Smelt Iron Ore to Iron Plate''"
definition "smeltIronPlate = Recipe
  [(iron_plate, 5)]
  [(steel_plate, 1)]
  16 electric_furnace STR ''Smelt Iron Plates to Steel Plate''"
definition "craftGear = Recipe
  [(iron_plate, 2)]
  [(iron_gear, 1)]
  0.5 assembling_machine_1 STR ''Craft Iron Plates into Iron Gear''"
definition "craftWagon = Recipe
  [(iron_gear, 10), (iron_plate, 20), (steel_plate, 20)]
  [(cargo_wagon, 1)]
  1 assembling_machine_1 STR ''Craft Iron Plates, Steel Plates and Iron Gears into Cargo Wagon''"

context begin
qualified lemmas defs =
  iron_plate_def steel_plate_def iron_gear_def iron_ore_def cargo_wagon_def
  electric_furnace_def assembling_machine_1_def
  smeltIronOre_def smeltIronPlate_def craftGear_def craftWagon_def
end

fun RFlow :: "item \<Rightarrow> rat \<Rightarrow> loc \<Rightarrow> (flow + mach_block, 'b) resource"
  where "RFlow i r l = Res (Inl (Flow i r l))"
fun RCentre :: "machine \<Rightarrow> nat \<Rightarrow> loc \<Rightarrow> loc \<Rightarrow> (flow + mach_block, 'b) resource"
  where "RCentre m n il ol = Res (Inr (MachBlock m n il ol))"

notation RFlow ("(_)[(_)] at (_)" [130, 60, 130] 130)
notation RCentre ("(_)<(_)> at (_) \<rightarrow> (_)" [130, 60, 130, 130] 130)

end