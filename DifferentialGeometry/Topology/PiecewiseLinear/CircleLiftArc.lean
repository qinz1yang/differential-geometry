/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LoopSpace.CircleLiftOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.exists_isPLHomeomorphOn_Icc_image_circleInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set E} (hJ : IsPLSphere 1 J) (e : loopCircle ≃ₜ J)
    {a b : ℝ} (hab : a < b) (hba : b < a + 1) :
    ∃ γ : ℝ → E,
      IsPLHomeomorphOn γ (Icc 0 1) ((fun t : ℝ => (e (t : loopCircle) : E)) '' Icc a b) ∧
      γ 0 = e (a : loopCircle) ∧ γ 1 = e (b : loopCircle) := by
  let g : ℝ → E := fun t => e (t : loopCircle)
  have hg : Continuous g :=
    continuous_subtype_val.comp (e.continuous.comp (AddCircle.continuous_mk' 1))
  have hinj : InjOn g (Ico a (a + 1)) := by
    intro s hs t ht hst
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hs ht).mp
      (e.injective (Subtype.ext hst))
  have hperiod : g (a + 1) = g a := by
    change (e ((a + 1 : ℝ) : loopCircle) : E) = (e (a : loopCircle) : E)
    rw [AddCircle.coe_add_period]
  have hpq : g a ≠ g b := by
    intro h
    exact hab.ne (hinj ⟨le_rfl, by linarith⟩ ⟨hab.le, hba⟩ h)
  have hunion : g '' Icc a b ∪ g '' Icc b (a + 1) = J := by
    apply Subset.antisymm
    · rintro _ (⟨t, -, rfl⟩ | ⟨t, -, rfl⟩) <;> exact (e _).property
    · intro y hy
      have hmem : e.symm ⟨y, hy⟩ ∈
          ((↑) : ℝ → loopCircle) '' Ico a (a + 1) := by
        rw [AddCircle.coe_image_Ico_eq]
        exact mem_univ _
      obtain ⟨t, ht, he⟩ := hmem
      have hgt : g t = y := by
        change (e (t : loopCircle) : E) = y
        rw [he, e.apply_symm_apply]
      by_cases htb : t ≤ b
      · exact Or.inl ⟨t, ⟨ht.1, htb⟩, hgt⟩
      · exact Or.inr ⟨t, ⟨(not_le.mp htb).le, ht.2.le⟩, hgt⟩
  have hinter : g '' Icc a b ∩ g '' Icc b (a + 1) = {g a, g b} := by
    apply Subset.antisymm
    · rintro y ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
      by_cases hta : t = a + 1
      · rw [hta, hperiod] at hts
        exact mem_insert_iff.mpr (Or.inl hts.symm)
      · have hst : s = t := hinj ⟨hs.1, hs.2.trans_lt hba⟩
          ⟨hab.le.trans ht.1, lt_of_le_of_ne ht.2 hta⟩ hts.symm
        have hsb : s = b := le_antisymm hs.2 (by simpa only [hst] using ht.1)
        rw [hsb]
        exact mem_insert_of_mem _ rfl
    · intro y hy
      rcases mem_insert_iff.mp hy with hy | hy
      · subst y
        exact ⟨⟨a, ⟨le_rfl, hab.le⟩, rfl⟩,
          ⟨a + 1, ⟨hba.le, le_rfl⟩, hperiod⟩⟩
      · have hy' : y = g b := mem_singleton_iff.mp hy
        subst y
        exact ⟨⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, ⟨b, ⟨le_rfl, hba.le⟩, rfl⟩⟩
  have hleft : (g '' Icc a b \ {g a, g b}).Nonempty := by
    let c := (a + b) / 2
    have hac : a < c := by dsimp [c]; linarith
    have hcb : c < b := by dsimp [c]; linarith
    refine ⟨g c, ⟨⟨c, ⟨hac.le, hcb.le⟩, rfl⟩, ?_⟩⟩
    intro hc
    rcases mem_insert_iff.mp hc with hc | hc
    · exact hac.ne' (hinj ⟨hac.le, hcb.trans hba⟩ ⟨le_rfl, by linarith⟩ hc)
    · exact hcb.ne (hinj ⟨hac.le, hcb.trans hba⟩ ⟨hab.le, hba⟩
        (mem_singleton_iff.mp hc))
  have hright : (g '' Icc b (a + 1) \ {g a, g b}).Nonempty := by
    let c := (b + (a + 1)) / 2
    have hbc : b < c := by dsimp [c]; linarith
    have hca : c < a + 1 := by dsimp [c]; linarith
    have hac : a < c := hab.trans hbc
    refine ⟨g c, ⟨⟨c, ⟨hbc.le, hca.le⟩, rfl⟩, ?_⟩⟩
    intro hc
    rcases mem_insert_iff.mp hc with hc | hc
    · exact hac.ne' (hinj ⟨hac.le, hca⟩ ⟨le_rfl, by linarith⟩ hc)
    · exact hbc.ne' (hinj ⟨hac.le, hca⟩ ⟨hab.le, hba⟩
        (mem_singleton_iff.mp hc))
  exact hJ.exists_isPLHomeomorphOn_Icc_of_union_eq_of_inter_eq_pair
    (isCompact_Icc.image hg).isClosed (isCompact_Icc.image hg).isClosed
    hunion hpq hinter hleft hright

end DifferentialGeometry.Topology.PiecewiseLinear
