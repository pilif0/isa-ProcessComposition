theory ProcessCategory
  imports
    ProcessComposition_PortGraph.ProcessPortGraph
    PortGraph.PortGraphTrans
    MonoidalCategory.MonoidalCategory
    ProcessesModuloPGs
    SymmetricCategory.SymmetricCategory
begin

section\<open>Category of Resources and Process Compositions\<close>

text\<open>
  We now formalise the category whose objects are resources and whose morphisms are equivalence
  classes of process compositions by @{const process_equiv}.
  In this context, when we mention a process or a composition we now mean the relevant equivalence
  class.
\<close>

(* TODO
  Many of the fact and locale names are not ideal if they ever occur in the same context as another
  category formalisation, since they could annoyingly overlap and shadow.
 *)

subsection\<open>Partial Magma\<close>

text\<open>Any two invalid compositions are equal\<close>
lemma invalid_unique:
  "\<lbrakk>\<not> valid x; \<not> valid y\<rbrakk> \<Longrightarrow> x = y"
  apply transfer
  unfolding process_equiv_def
  by transfer simp

text\<open>
  The category theory formalisation uses contravariant composition, so we need to swap order of our
  sequential composition.

  We mainly use this variant where necessary and swap to our order otherwise.
\<close>
abbreviation "Seq' x y \<equiv> Seq y x"

text\<open>Prove that this is a partial magma\<close>
lemma par_mag:
  "partial_magma Seq'"
proof
  let ?n = "Seq (Identity Empty) (Identity Anything)"

  have "Seq f ?n = ?n \<and> Seq ?n f = ?n" for f
    apply transfer
    unfolding process_equiv_def
    apply transfer
    by simp
  moreover have "\<forall>f. Seq f n = n \<and> Seq n f = n \<Longrightarrow> n = ?n" for n
    by (metis calculation)
  ultimately show "\<exists>!n. \<forall>f. Seq' n f = n \<and> Seq' f n = n"
    by blast
qed

interpretation par_mag: partial_magma Seq'
  using par_mag .

subsection\<open>Partial Composition\<close>

lemma par_comp:
  "partial_composition Seq'"
  using par_mag by unfold_locales

interpretation par_comp: partial_composition Seq'
  using par_comp .

subsection\<open>Category\<close>

lemma invalid_imp_null:
  "\<not> valid p \<Longrightarrow> p = par_mag.null"
  apply (rule par_mag.null_eqI)
  apply transfer
  unfolding process_equiv_def
  apply transfer
  apply simp
  done

lemma null_witness:
  "par_mag.null = Seq (Identity Empty) (Identity Anything)" (is "_ = ?n")
proof -
  have "Seq ?n f = ?n \<and> Seq f ?n = ?n" for f
    apply transfer
    unfolding process_equiv_def
    apply transfer
    by simp
  moreover have "\<forall>f. Seq n f = n \<and> Seq f n = n \<Longrightarrow> n = ?n" for n
    by (metis calculation)
  ultimately show ?thesis
    using par_mag.null_def by simp
qed

lemma null_invalid [simp]:
 "\<not> valid par_mag.null"
  unfolding null_witness
  by (transfer, transfer, simp)

lemma not_null_eq_valid [simp]:
  "x \<noteq> par_mag.null \<equiv> valid x"
  by (smt (verit) invalid_unique null_invalid)

lemma null_eq_invalid [simp]:
  "x = par_mag.null \<equiv> \<not> valid x"
  using not_null_eq_valid by (smt (verit))

lemma ide_simp:
  "par_comp.ide x = (\<exists>a. x = Identity a)"
proof
  show "par_comp.ide x \<Longrightarrow> \<exists>a. x = Identity a"
    unfolding par_comp.ide_def not_null_eq_valid
    apply clarsimp
    apply transfer
    unfolding process_equiv_def
    apply transfer
    using pgConstruct_ide_input by force
  show "\<exists>a. x = Identity a \<Longrightarrow> par_comp.ide x"
    unfolding par_comp.ide_def not_null_eq_valid
    apply clarsimp
    apply transfer
    unfolding process_equiv_def
    apply transfer
    using pgConstruct_seq_unitL_pgEquiv pgConstruct_seq_unitR_pgEquiv by fastforce
qed

lemma domains_simp [simp]:
  "valid x \<Longrightarrow> par_comp.domains x = {Identity (input x)}"
  "\<not> valid x \<Longrightarrow> par_comp.domains x = {}"
  unfolding par_comp.domains_def ide_simp not_null_eq_valid
  by fastforce+

lemma codomains_simp [simp]:
  "valid x \<Longrightarrow> par_comp.codomains x = {Identity (output x)}"
  "\<not> valid x \<Longrightarrow> par_comp.codomains x = {}"
  unfolding par_comp.codomains_def ide_simp not_null_eq_valid
  by fastforce+

lemma arr_simp [simp]:
  "par_comp.arr x = valid x"
  by (cases "valid x" ; simp add: par_comp.arr_def)

lemma dom_simp [simp]:
  "par_comp.dom x = (if valid x then Identity (input x) else par_mag.null)"
  by (simp add: par_comp.dom_def)

lemma cod_simp [simp]:
  "par_comp.cod x = (if valid x then Identity (output x) else par_mag.null)"
  by (simp add: par_comp.cod_def)

lemma cat:
  "category Seq'"
proof (intro category.intro)
  show "partial_composition Seq'"
    using par_comp .

  show "category_axioms Seq'"
  proof
    fix f g
    show "Seq' g f \<noteq> par_mag.null \<Longrightarrow> par_comp.seq g f"
      by simp
  next
    fix f 
    show "(par_comp.domains f \<noteq> {}) = (par_comp.codomains f \<noteq> {})"
      by (cases "valid f" ; simp)
  next
    fix f g h
    show "\<lbrakk>par_comp.seq h g; par_comp.seq (Seq' h g) f\<rbrakk> \<Longrightarrow> par_comp.seq g f"
      by simp
  next
    fix f g h
    show "\<lbrakk>par_comp.seq h (Seq' g f); par_comp.seq g f\<rbrakk> \<Longrightarrow> par_comp.seq h g"
      by fastforce
  next
    fix f g h
    show "\<lbrakk>par_comp.seq g f; par_comp.seq h g\<rbrakk> \<Longrightarrow> par_comp.seq (Seq' h g) f"
      by simp
  next
    fix f g h
    show "\<lbrakk>par_comp.seq g f; par_comp.seq h g\<rbrakk> \<Longrightarrow> Seq' (Seq' h g) f = Seq' h (Seq' g f)"
      apply (cases "valid (Seq' h g)" ; cases "valid (Seq' g f)" ; clarsimp)
      apply transfer
      apply (simp add: process_equiv_def)
      apply transfer
      apply clarsimp
      using pgConstruct_Seq_assoc pgEquiv_sym by metis
  qed
qed

interpretation cat: category Seq'
  using cat .

text\<open>Thus we can form product categories\<close>
interpretation prod_cat: product_category Seq' Seq' by unfold_locales
interpretation prod_prod_cat: product_category Seq' prod_cat.comp by unfold_locales

subsection\<open>@{const Par} is a Binary Endofunctor\<close>

lemma Identity_eq_simp:
  "(Identity x = Identity y) = (x = y)"
  apply transfer
  apply (simp add: process_equiv_def)
  apply transfer
  by fastforce

lemma Par_Identity_simp [simp]:
  "Par (Identity x) (Identity y) = Identity (x \<odot> y)"
  apply transfer
  apply (simp add: process_equiv_def)
  apply transfer
  apply clarsimp
  by (simp add: pgConstruct_id_merge)

lemma iso_Identity:
  "cat.iso (Identity x)"
  using cat.comp_ide_self by (fastforce simp add: cat.iso_def cat.inverse_arrows_def ide_simp)

lemma process_interchange:
  assumes "valid f1"
      and "valid f2"
      and "valid g1"
      and "valid g2"
      and "output f1 = input g1"
      and "output f2 = input g2"
    shows "Par (Seq f1 g1) (Seq f2 g2) = Seq (Par f1 f2) (Par g1 g2)"
  using assms
  apply transfer
  apply (simp add: process_equiv_def)
  apply transfer
  by (simp add: pgConstruct_interchange)

lemma prod_cat_comp_valid_fst:
  "valid (fst (prod_cat.comp (g1, g2) (f1, f2))) = (valid f1 \<and> valid g1 \<and> output f1 = input g1 \<and> valid f2 \<and> valid g2 \<and> output f2 = input g2)"
  by (clarsimp simp add: prod_cat.comp_def) (fastforce simp add: Identity_eq_simp)

lemma prod_cat_comp_valid_snd:
  "valid (snd (prod_cat.comp (g1, g2) (f1, f2))) = (valid f1 \<and> valid g1 \<and> output f1 = input g1 \<and> valid f2 \<and> valid g2 \<and> output f2 = input g2)"
  by (clarsimp simp add: prod_cat.comp_def) (fastforce simp add: Identity_eq_simp)

lemma bi_endo:
  "binary_endofunctor Seq' (\<lambda>(x, y). Par x y)"
proof
  fix f :: "('y, 'z, 'aa, 'ab) eq_process \<times> ('y, 'z, 'aa, 'ab) eq_process"
  obtain f1 f2 where f [simp]: "f = (f1, f2)"
    using prod.exhaust by metis

  show "\<not> prod_cat.arr f \<Longrightarrow> (case f of (x, y) \<Rightarrow> Par x y) = par_mag.null"
    by simp
  show "prod_cat.arr f \<Longrightarrow> par_comp.arr (case f of (x, y) \<Rightarrow> Par x y)"
    by simp
  show "prod_cat.arr f \<Longrightarrow> par_comp.dom (case f of (x, y) \<Rightarrow> Par x y) = (case prod_cat.dom f of (x, y) \<Rightarrow> Par x y)"
    by simp
  show "prod_cat.arr f \<Longrightarrow> par_comp.cod (case f of (x, y) \<Rightarrow> Par x y) = (case prod_cat.cod f of (x, y) \<Rightarrow> Par x y)"
    by simp

  fix g :: "('y, 'z, 'aa, 'ab) eq_process \<times> ('y, 'z, 'aa, 'ab) eq_process"
  obtain g1 g2 where f [simp]: "g = (g1, g2)"
    using prod.exhaust by metis

  show "prod_cat.seq g f \<Longrightarrow> (case prod_cat.comp g f of (x, y) \<Rightarrow> Par x y) = Seq' (case g of (x, y) \<Rightarrow> Par x y) (case f of (x, y) \<Rightarrow> Par x y)"
    by (simp add: process_interchange prod_cat_comp_valid_fst)
qed

interpretation bi_endo: binary_endofunctor Seq' "\<lambda>(x, y). Par x y"
  using bi_endo .

subsection\<open>Monoidal Category\<close>

lemma par_assoc:
  assumes "valid x"
      and "valid y"
      and "valid z"
    shows "Par (Par x y) z = Par x (Par y z)"
  using assms
  apply transfer
  apply (simp add: process_equiv_def)
  apply transfer
  by (simp add: pgConstruct_Par_assoc)

lemma prod_prod_cat_comp_valid_fst:
  "valid (fst (prod_prod_cat.comp (g1, g2, g3) (f1, f2, f3))) =
  (valid f1 \<and> valid g1 \<and> output f1 = input g1 \<and> valid f2 \<and> valid g2 \<and> output f2 = input g2 \<and> valid f3 \<and> valid g3 \<and> output f3 = input g3)"
  by (clarsimp simp add: prod_prod_cat.comp_def) (fastforce simp add: Identity_eq_simp)

lemma prod_prod_cat_comp_valid_fst_snd:
  "valid (fst (snd (prod_prod_cat.comp (g1, g2, g3) (f1, f2, f3)))) =
  (valid f1 \<and> valid g1 \<and> output f1 = input g1 \<and> valid f2 \<and> valid g2 \<and> output f2 = input g2 \<and> valid f3 \<and> valid g3 \<and> output f3 = input g3)"
  by (clarsimp simp add: prod_prod_cat.comp_def) (fastforce simp add: Identity_eq_simp)

lemma prod_prod_cat_comp_valid_snd_snd:
  "valid (snd (snd (prod_prod_cat.comp (g1, g2, g3) (f1, f2, f3)))) =
  (valid f1 \<and> valid g1 \<and> output f1 = input g1 \<and> valid f2 \<and> valid g2 \<and> output f2 = input g2 \<and> valid f3 \<and> valid g3 \<and> output f3 = input g3)"
  by (clarsimp simp add: prod_prod_cat.comp_def) (fastforce simp add: Identity_eq_simp)

lemma identity_functor_simp1:
  "identity_functor.map Seq' x = Par (Identity Empty) x"
proof (cases "valid x")
  case True
  then show ?thesis
    apply (simp add: cat.map_def)
    apply transfer
    apply (simp add: process_equiv_def)
    apply transfer
    by (clarsimp simp add: pgConstruct_par_unitL_pgEquiv pgEquiv_sym)
next
  case False
  then show ?thesis by (simp add: cat.map_def invalid_unique)
qed

lemma identity_functor_simp2:
  "identity_functor.map Seq' x = Par x (Identity Empty)"
proof (cases "valid x")
  case True
  then show ?thesis
    apply (simp add: cat.map_def)
    apply transfer
    apply (simp add: process_equiv_def)
    apply transfer
    by (clarsimp simp add: pgConstruct_par_unitR_pgEquiv pgEquiv_sym)
next
  case False
  then show ?thesis by (simp add: cat.map_def invalid_unique)
qed

lemma moncat:
  "monoidal_category Seq' (case_prod Par) (\<lambda>(x, y, z). Par x (Par y z)) (Identity Empty)"
proof (intro monoidal_category.intro)
  show "category Seq'"
    using cat .

  show "product_category Seq' Seq'"
    by unfold_locales

  show "product_category Seq' prod_cat.comp"
    by unfold_locales

  show "binary_endofunctor Seq' (\<lambda>(x, y). Par x y)"
    using bi_endo .

  show
    " natural_isomorphism
        prod_prod_cat.comp
        Seq'
        bi_endo.ToTC
        bi_endo.ToCT
        (\<lambda>(x, y, z). Par x (Par y z))"
    apply (unfold_locales ; clarsimp simp add: bi_endo.ToTC_def bi_endo.ToCT_def ide_simp iso_Identity prod_prod_cat_comp_valid_fst process_interchange)
    apply (simp add: cat.comp_arr_dom)
    apply (simp add: cat.comp_cod_arr par_assoc)
    done

  show "equivalence_functor Seq' Seq' (\<lambda>f. case (par_comp.cod (Identity Empty), f) of (x, xa) \<Rightarrow> Par x xa)"
    apply (unfold_locales ; clarsimp)
     apply (metis arr_simp cat.comp_arr_dom dom_simp input_simps(2) output_simps(2) process_interchange valid_simps(2))
    apply (rule equivalence_functor.induces_equivalence)
    using cat.is_equivalence[unfolded identity_functor_simp1[abs_def]] .

  show "equivalence_functor Seq' Seq' (\<lambda>f. case (f, par_comp.cod (Identity Empty)) of (x, xa) \<Rightarrow> Par x xa)"
    apply (unfold_locales ; clarsimp)
     apply (metis arr_simp cat.comp_arr_dom dom_simp input_simps(2) output_simps(2) process_interchange valid_simps(2))
    apply (rule equivalence_functor.induces_equivalence)
    using cat.is_equivalence[unfolded identity_functor_simp2[abs_def]] .

  show "monoidal_category_axioms Seq' (\<lambda>(x, y). Par x y) (\<lambda>(x, y, z). Par x (Par y z)) (Identity Empty)"
    apply (unfold_locales)
      apply (clarsimp simp add: par_comp.in_hom_def)
    using cat.comp_ide_self apply (fastforce simp add: cat.iso_def cat.inverse_arrows_def ide_simp)
    apply (clarsimp simp add: ide_simp)
    by (metis cat.comp_ide_self ide_simp)
qed

subsection\<open>Symmetric Monoidal Category\<close>

lemma seq_swap_identity:
  "Seq (Swap a b) (Identity (b \<odot> a)) = Swap a b"
  by (metis cat.ext ide_simp input_simps(2) null_invalid output_simps(3) par_comp.comp_ide_arr valid_simps(2) valid_simps(3) valid_simps(4))

lemma swap_par_natural:
  "Seq (Swap (input x) (input y)) (Par y x) = Seq (Par x y) (Swap (output x) (output y))"
  apply transfer
  apply (simp add: process_equiv_def)
  apply transfer
  apply (safe, simp_all)
  oops

text\<open>Prove that this is a symmetric monoidal category\<close>
lemma symoncat:
  "symmetric_monoidal_category Seq' (case_prod Par) (\<lambda>(x, y, z). Par x (Par y z)) (Identity Empty)
    (\<lambda>(x, y). Seq (Swap (input x) (input y)) (Seq (Par y x) (Swap (output y) (output x))))"
proof (intro symmetric_monoidal_category.intro braided_monoidal_category.intro)
  show "monoidal_category Seq' (\<lambda>(x, y). Par x y) (\<lambda>(x, y, z). Par x (Par y z)) (Identity Empty)"
    using moncat .

  show "natural_isomorphism prod_cat.comp Seq' (\<lambda>(x, y). Par x y) bi_endo.sym
     (\<lambda>(x, y).
         Seq' (Seq' (Swap (output y) (output x))
                    (Par y x))
              (Swap (input x) (input y)))"
    sorry
  show "inverse_transformation prod_cat.comp Seq' (\<lambda>(x, y). Par x y) bi_endo.sym
    (\<lambda>(x, y).
      Seq' (Seq' (Swap (output y) (output x))
                 (Par y x))
           (Swap (input x) (input y)))"
    sorry
  show "braided_monoidal_category_axioms Seq'
    (\<lambda>(x, y). Par x y) (\<lambda>(x, y, z). Par x (Par y z))
    (\<lambda>(x, y).
      Seq' (Seq' (Swap (output y) (output x))
                 (Par y x))
           (Swap (input x) (input y)))"
    sorry
  show "symmetric_monoidal_category_axioms Seq' (\<lambda>(x, y). Par x y)
    (\<lambda>(x, y).
      Seq' (Seq' (Swap (output y) (output x))
                 (Par y x))
           (Swap (input x) (input y)))"
    sorry
  oops

end
