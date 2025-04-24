theory ProcessPG_Util
  imports Main
begin

section\<open>Utility Theorems\<close>

text\<open>
  This theory contains general facts that we use in our proof but which do not depend on our
  development.
\<close>

lemma fst_set_zip [simp]:
  "length xs = length ys \<Longrightarrow> fst ` set (zip xs ys) = set xs"
  by (metis list.set_map map_fst_zip)
lemma snd_set_zip [simp]:
  "length xs = length ys \<Longrightarrow> snd ` set (zip xs ys) = set ys"
  by (metis list.set_map map_snd_zip)

end