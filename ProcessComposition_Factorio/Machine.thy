theory Machine
  imports
    Location
    HOL.Rat
begin

section\<open>Machine Blocks\<close>

text\<open>
  Machines are defined by:
  \<^item> String label,
  \<^item> Production speed,
  \<^item> Electricity drain (base), and
  \<^item> Electricity consumption (running).
\<close>
datatype machine =
  Machine (machineLabel: String.literal) (machineSpeed: rat) (machineDrain: nat) (machineConsu: nat)

text\<open>
  Machine blocks are groups of machines with common input and output locations which are meant to
  perform the same recipe in parallel.
  They are defined by the machine type, count, input location and output location.
\<close>
datatype mach_block =
  MachBlock (mblockMach: machine) (mblockCount: nat) (mblockIn: loc) (mblockOut: loc)

(* Note: convenient notation for machines is introduced in TestingPrelims.thy *)

end