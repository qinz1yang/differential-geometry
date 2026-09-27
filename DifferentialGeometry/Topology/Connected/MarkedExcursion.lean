/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Rolle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Topology

namespace DifferentialGeometry.Topology

private theorem exists_marked_excursion_of_unmarked_max
    {Y : Type*} [ConditionallyCompleteLinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
    {f : ℝ → Y} (hf : Continuous f) {P : Set Y} {a b x : ℝ}
    (hab : a < b) (heq : f a = f b) (haP : f a ∈ P)
    (hfinite : (P ∩ f '' Icc a b).Finite) (hx : x ∈ Ioo a b)
    (hmax : IsMaxOn f (Icc a b) x) (hxP : f x ∉ P) :
    ∃ c d, a ≤ c ∧ c < d ∧ d ≤ b ∧ f c = f d ∧ f c ∈ P ∧
      ∀ t ∈ Ioo c d, f t ∉ P := by
  let W := P ∩ f '' Icc a b
  have haW : f a ∈ W := ⟨haP, a, ⟨le_rfl, hab.le⟩, rfl⟩
  have hvW : sSup W ∈ W := (show W.Nonempty from ⟨f a, haW⟩).csSup_mem hfinite
  have hav : f a ≤ sSup W := le_csSup hfinite.bddAbove haW
  have hvx : sSup W < f x := by
    obtain ⟨y, hy, hyf⟩ := hvW.2
    have hle : sSup W ≤ f x := hyf ▸ hmax hy
    exact lt_of_le_of_ne hle fun he => hxP (he ▸ hvW.1)
  let L := Icc a x ∩ f ⁻¹' {sSup W}
  let R := Icc x b ∩ f ⁻¹' {sSup W}
  have hL : IsCompact L := isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  have hR : IsCompact R := isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  have hLne : L.Nonempty := by
    obtain ⟨y, hy, hyf⟩ := intermediate_value_Icc hx.1.le hf.continuousOn ⟨hav, hvx.le⟩
    exact ⟨y, hy, hyf⟩
  have hRne : R.Nonempty := by
    have hbv : f b ≤ sSup W := heq ▸ hav
    obtain ⟨y, hy, hyf⟩ := intermediate_value_Icc' hx.2.le hf.continuousOn ⟨hbv, hvx.le⟩
    exact ⟨y, hy, hyf⟩
  obtain ⟨c, hc, hcle⟩ := hL.exists_isMaxOn hLne continuous_id.continuousOn
  obtain ⟨d, hd, hdle⟩ := hR.exists_isMinOn hRne continuous_id.continuousOn
  have hcf : f c = sSup W := hc.2
  have hdf : f d = sSup W := hd.2
  have hcx : c < x := by
    refine lt_of_le_of_ne hc.1.2 ?_
    intro he
    exact hvx.ne (hcf ▸ congrArg f he)
  have hxd : x < d := by
    refine lt_of_le_of_ne hd.1.1 ?_
    intro he
    exact hvx.ne (hdf ▸ congrArg f he).symm
  refine ⟨c, d, hc.1.1, hcx.trans hxd, hd.1.2, hcf.trans hdf.symm,
    hcf.symm ▸ hvW.1, ?_⟩
  intro t ht htP
  have htI : t ∈ Icc a b := ⟨hc.1.1.trans ht.1.le, ht.2.le.trans hd.1.2⟩
  have htv : f t ≤ sSup W := le_csSup hfinite.bddAbove ⟨htP, t, htI, rfl⟩
  by_cases htx : t ≤ x
  · obtain ⟨y, hy, hyf⟩ := intermediate_value_Icc htx hf.continuousOn ⟨htv, hvx.le⟩
    have hyL : y ∈ L := ⟨⟨htI.1.trans hy.1, hy.2⟩, hyf⟩
    have hyc : y ≤ c := hcle hyL
    linarith [ht.1, hy.1]
  · obtain ⟨y, hy, hyf⟩ :=
      intermediate_value_Icc' (le_of_not_ge htx) hf.continuousOn ⟨htv, hvx.le⟩
    have hyR : y ∈ R := ⟨⟨hy.1, hy.2.trans htI.2⟩, hyf⟩
    have hdy : d ≤ y := hdle hyR
    linarith [ht.2, hy.2]

theorem exists_marked_excursion_of_eq_endpoints
    {f : ℝ → ℝ} (hf : Continuous f) {P : Set ℝ} {a b : ℝ}
    (hab : a < b) (heq : f a = f b) (haP : f a ∈ P)
    (hfinite : (P ∩ f '' Icc a b).Finite)
    (hno : ∀ t ∈ Ioo a b, f t ∈ P → ¬ IsLocalMax f t ∧ ¬ IsLocalMin f t) :
    ∃ c d, a ≤ c ∧ c < d ∧ d ≤ b ∧ f c = f d ∧ f c ∈ P ∧
      ∀ t ∈ Ioo c d, f t ∉ P := by
  obtain ⟨x, hx, hextr⟩ := exists_Ioo_extr_on_Icc hab hf.continuousOn heq
  rcases hextr with hmin | hmax
  · have hxP : f x ∉ P := fun hp =>
      (hno x hx hp).2 (IsMinOn.isLocalMin hmin (Icc_mem_nhds hx.1 hx.2))
    exact exists_marked_excursion_of_unmarked_max (Y := ℝᵒᵈ)
      hf hab heq haP hfinite hx hmin hxP
  · have hxP : f x ∉ P := fun hp =>
      (hno x hx hp).1 (IsMaxOn.isLocalMax hmax (Icc_mem_nhds hx.1 hx.2))
    exact exists_marked_excursion_of_unmarked_max hf hab heq haP hfinite hx hmax hxP

theorem exists_repeated_level_of_unit_shift
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : a < b) (hba : b < a + 1) (hshift : f (a + 1) = f a + 1)
    (hmod : ∃ k : ℤ, f b - f a = (k : ℝ)) :
    ∃ c d, a ≤ c ∧ c < d ∧ d ≤ a + 1 ∧ d < c + 1 ∧ f c = f d ∧
      (f c = f a ∨ f c = f a + 1) := by
  obtain ⟨k, hk⟩ := hmod
  by_cases hk0 : k ≤ 0
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    have hfb : f b ≤ f a := by linarith
    obtain ⟨d, hd, hdf⟩ := intermediate_value_Icc hba.le hf.continuousOn
      (show f a ∈ Icc (f b) (f (a + 1)) from ⟨hfb, by linarith⟩)
    have hda : d < a + 1 := by
      refine lt_of_le_of_ne hd.2 ?_
      intro he
      rw [he, hshift] at hdf
      linarith
    exact ⟨a, d, le_rfl, hab.trans_le hd.1, hd.2, hda, hdf.symm, Or.inl rfl⟩
  · have hk1 : (1 : ℤ) ≤ k := by omega
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hfb : f a + 1 ≤ f b := by linarith
    obtain ⟨c, hc, hcf⟩ := intermediate_value_Icc hab.le hf.continuousOn
      (show f a + 1 ∈ Icc (f a) (f b) from ⟨by linarith, hfb⟩)
    have hac : a < c := by
      refine lt_of_le_of_ne hc.1 ?_
      intro he
      rw [← he] at hcf
      linarith
    exact ⟨c, a + 1, hc.1, hc.2.trans_lt hba, le_rfl, by linarith,
      hcf.trans hshift.symm, Or.inr hcf⟩

theorem exists_repeated_level_of_unit_shift_or_neg
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hab : a < b) (hba : b < a + 1)
    (hshift : f (a + 1) = f a + 1 ∨ f (a + 1) = f a - 1)
    (hmod : ∃ k : ℤ, f b - f a = (k : ℝ)) :
    ∃ c d, a ≤ c ∧ c < d ∧ d ≤ a + 1 ∧ d < c + 1 ∧ f c = f d ∧
      (f c = f a ∨ f c = f a + 1 ∨ f c = f a - 1) := by
  rcases hshift with hplus | hminus
  · obtain ⟨c, d, hac, hcd, hda, hshort, heq, hlevel⟩ :=
      exists_repeated_level_of_unit_shift hf hab hba hplus hmod
    exact ⟨c, d, hac, hcd, hda, hshort, heq, hlevel.imp_right Or.inl⟩
  · have hgshift : -f (a + 1) = -f a + 1 := by linarith
    have hgmod : ∃ k : ℤ, -f b - -f a = (k : ℝ) := by
      obtain ⟨k, hk⟩ := hmod
      refine ⟨-k, ?_⟩
      push_cast
      linarith
    obtain ⟨c, d, hac, hcd, hda, hshort, heq, hlevel⟩ :=
      exists_repeated_level_of_unit_shift hf.neg hab hba hgshift hgmod
    simp only [Pi.neg_apply] at heq hlevel
    refine ⟨c, d, hac, hcd, hda, hshort, by linarith, ?_⟩
    rcases hlevel with hlevel | hlevel
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inr (by linarith))

theorem exists_periodic_marked_excursion
    {f : ℝ → ℝ} (hf : Continuous f) {P : Set ℝ}
    (hperiod : (∀ t, f (t + 1) = f t + 1) ∨ (∀ t, f (t + 1) = f t - 1))
    (hP : ∀ y, y + 1 ∈ P ↔ y ∈ P)
    (hfinite : ∀ a b, (P ∩ f '' Icc a b).Finite)
    (hno : ∀ t, f t ∈ P → ¬ IsLocalMax f t ∧ ¬ IsLocalMin f t)
    {a b : ℝ} (hab : a < b) (hba : b < a + 1) (haP : f a ∈ P)
    (hmod : ∃ k : ℤ, f b - f a = (k : ℝ)) :
    ∃ c d, c < d ∧ d < c + 1 ∧ f c = f d ∧ f c ∈ P ∧
      ∀ t ∈ Ioo c d, f t ∉ P := by
  obtain ⟨u, v, -, huv, -, hshort, heq, hlevel⟩ :=
    exists_repeated_level_of_unit_shift_or_neg hf hab hba
      (hperiod.imp (fun h => h a) (fun h => h a)) hmod
  have huP : f u ∈ P := by
    rcases hlevel with hlevel | hlevel | hlevel
    · rwa [hlevel]
    · rw [hlevel]
      exact (hP (f a)).mpr haP
    · rw [hlevel]
      apply (hP (f a - 1)).mp
      convert haP using 1
      ring
  obtain ⟨c, d, huc, hcd, hdv, hfeq, hcP, hfree⟩ :=
    exists_marked_excursion_of_eq_endpoints hf huv heq huP (hfinite u v)
      (fun t _ => hno t)
  exact ⟨c, d, hcd, by linarith, hfeq, hcP, hfree⟩

end DifferentialGeometry.Topology
