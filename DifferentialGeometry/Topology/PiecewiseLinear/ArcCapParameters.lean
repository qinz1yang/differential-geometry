/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalInterpolation
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.image_Icc_eq_segment_of_segment_subset
    {γ : ℝ → E} {T : Set E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) T)
    {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hst : s ≤ t)
    (hseg : segment ℝ (γ s) (γ t) ⊆ T) :
    γ '' Icc s t = segment ℝ (γ s) (γ t) := by
  rcases eq_or_lt_of_le hst with rfl | hst
  · simp
  let q : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (γ s) (γ t)
  have hqimg : q '' Icc 0 1 = segment ℝ (γ s) (γ t) :=
    (segment_eq_image_lineMap ℝ _ _).symm
  have hqT : MapsTo q (Icc 0 1) T := fun u hu => hseg (hqimg.subset ⟨u, hu, rfl⟩)
  let g : ℝ → ℝ := Function.invFunOn γ (Icc 0 1) ∘ q
  have hgc : ContinuousOn g (Icc 0 1) :=
    hγ.symm.isPiecewiseAffineOn.continuousOn.comp q.continuous_of_finiteDimensional.continuousOn hqT
  have hqne : γ s ≠ γ t := fun h => hst.ne (hγ.bijOn.injOn hs ht h)
  have hginj : InjOn g (Icc 0 1) :=
    hγ.symm.bijOn.injOn.comp (AffineMap.lineMap_injective ℝ hqne).injOn hqT
  have hg0 : g 0 = s := by
    change Function.invFunOn γ (Icc 0 1) (AffineMap.lineMap (γ s) (γ t) 0) = s
    rw [AffineMap.lineMap_apply_zero, hγ.bijOn.invOn_invFunOn.1 hs]
  have hg1 : g 1 = t := by
    change Function.invFunOn γ (Icc 0 1) (AffineMap.lineMap (γ s) (γ t) 1) = t
    rw [AffineMap.lineMap_apply_one, hγ.bijOn.invOn_invFunOn.1 ht]
  have hgmono : StrictMonoOn g (Icc 0 1) :=
    hgc.strictMonoOn_of_injOn_Icc zero_le_one (by rw [hg0, hg1]; exact hst.le) hginj
  have hgimg : g '' Icc 0 1 = Icc s t := by
    rw [hgc.image_Icc_of_monotoneOn zero_le_one hgmono.monotoneOn, hg0, hg1]
  rw [← hgimg, image_image]
  exact (image_congr fun u hu => hγ.bijOn.invOn_invFunOn.2 (hqT hu)).trans hqimg

theorem IsPLHomeomorphOn.exists_parametrization_terminal_segments
    {γ : ℝ → E} {T D₀ D₁ : Set E} {x₀ x x₁ : E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) T)
    (h₀ : T ∩ D₀ = segment ℝ (γ 0) x₀) (h₁ : T ∩ D₁ = segment ℝ (γ 1) x₁)
    (hne₀ : γ 0 ≠ x₀) (hne₁ : γ 1 ≠ x₁) (hx : x ∈ T \ (D₀ ∪ D₁)) :
    ∃ δ : ℝ → E, IsPLHomeomorphOn δ (Icc 0 1) T ∧
      δ 0 = γ 0 ∧ δ (1 / 4) = x₀ ∧ δ (1 / 2) = x ∧
      δ (3 / 4) = x₁ ∧ δ 1 = γ 1 := by
  have hx₀ : x₀ ∈ T ∩ D₀ := h₀.symm ▸ right_mem_segment ℝ (γ 0) x₀
  have hx₁ : x₁ ∈ T ∩ D₁ := h₁.symm ▸ right_mem_segment ℝ (γ 1) x₁
  obtain ⟨a, ha, hγa⟩ := hγ.bijOn.surjOn hx₀.1
  obtain ⟨b, hb, hγb⟩ := hγ.bijOn.surjOn hx.1
  obtain ⟨c, hc, hγc⟩ := hγ.bijOn.surjOn hx₁.1
  have ha0 : 0 < a := lt_of_le_of_ne ha.1 fun heq => hne₀ (heq.symm ▸ hγa)
  have hc1 : c < 1 := lt_of_le_of_ne hc.2 fun heq => hne₁ (heq ▸ hγc)
  have hlow : γ '' Icc 0 a = T ∩ D₀ := by
    rw [hγ.image_Icc_eq_segment_of_segment_subset ⟨le_rfl, zero_le_one⟩ ha ha.1
      (by rw [hγa, ← h₀]; exact inter_subset_left), hγa, ← h₀]
  have hhigh : γ '' Icc c 1 = T ∩ D₁ := by
    rw [hγ.image_Icc_eq_segment_of_segment_subset hc ⟨zero_le_one, le_rfl⟩ hc.2
      (by rw [hγc, segment_symm, ← h₁]; exact inter_subset_left), hγc, segment_symm, ← h₁]
  have hab : a < b := by
    by_contra! hba
    exact hx.2 (Or.inl (hlow.subset ⟨b, ⟨hb.1, hba⟩, hγb⟩).2)
  have hbc : b < c := by
    by_contra! hcb
    exact hx.2 (Or.inr (hhigh.subset ⟨b, ⟨hcb, hb.2⟩, hγb⟩).2)
  obtain ⟨δ, hδ, hδ₀, hδa, hδb, hδc, hδ₁⟩ :=
    hγ.exists_parametrization_three_points ha0 hab hbc hc1
  exact ⟨δ, hδ, hδ₀, hδa.trans hγa, hδb.trans hγb, hδc.trans hγc, hδ₁⟩

theorem IsPLHomeomorphOn.exists_mem_sdiff_of_disjoint_terminal_segments
    {γ : ℝ → E} {T D₀ D₁ : Set E} {x₀ x₁ : E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) T)
    (h₀ : T ∩ D₀ = segment ℝ (γ 0) x₀) (h₁ : T ∩ D₁ = segment ℝ (γ 1) x₁)
    (hdis : Disjoint D₀ D₁) : (T \ (D₀ ∪ D₁)).Nonempty := by
  have hx₀ : x₀ ∈ T ∩ D₀ := h₀.symm ▸ right_mem_segment ℝ (γ 0) x₀
  have hx₁ : x₁ ∈ T ∩ D₁ := h₁.symm ▸ right_mem_segment ℝ (γ 1) x₁
  obtain ⟨a, ha, hγa⟩ := hγ.bijOn.surjOn hx₀.1
  obtain ⟨c, hc, hγc⟩ := hγ.bijOn.surjOn hx₁.1
  have hlow : γ '' Icc 0 a = T ∩ D₀ := by
    rw [hγ.image_Icc_eq_segment_of_segment_subset ⟨le_rfl, zero_le_one⟩ ha ha.1
      (by rw [hγa, ← h₀]; exact inter_subset_left), hγa, ← h₀]
  have hhigh : γ '' Icc c 1 = T ∩ D₁ := by
    rw [hγ.image_Icc_eq_segment_of_segment_subset hc ⟨zero_le_one, le_rfl⟩ hc.2
      (by rw [hγc, segment_symm, ← h₁]; exact inter_subset_left), hγc, segment_symm, ← h₁]
  have hac : a < c := by
    by_contra! hca
    exact disjoint_left.mp hdis (hlow.subset ⟨c, ⟨hc.1, hca⟩, hγc⟩).2 hx₁.2
  let b := (a + c) / 2
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [b]; linarith [ha.1, hc.1],
    by dsimp [b]; linarith [ha.2, hc.2]⟩
  refine ⟨γ b, hγ.bijOn.mapsTo hb, ?_⟩
  rintro (hmem | hmem)
  · obtain ⟨t, ht, htb⟩ := hlow.symm.subset ⟨hγ.bijOn.mapsTo hb, hmem⟩
    have htb' : t = b := hγ.bijOn.injOn ⟨ht.1, ht.2.trans ha.2⟩ hb htb
    dsimp [b] at htb'
    linarith [ht.2]
  · obtain ⟨t, ht, htb⟩ := hhigh.symm.subset ⟨hγ.bijOn.mapsTo hb, hmem⟩
    have htb' : t = b := hγ.bijOn.injOn ⟨hc.1.trans ht.1, ht.2⟩ hb htb
    dsimp [b] at htb'
    linarith [ht.1]

theorem eq_of_cap_boundary_singletons_of_inter_eq
    {A B C : Set E} {q r : (Fin 3 → ℝ) → E} {x y : E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) C)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) C)
    (hA : q '' stdSimplexBoundary 2 ∩ A = {x})
    (hB : r '' stdSimplexBoundary 2 ∩ B = {y}) (hAB : A ∩ C = B ∩ C) : x = y := by
  have hbd : q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 :=
    hq.image_stdSimplexBoundary_congr hr
  have hbdC : q '' stdSimplexBoundary 2 ⊆ C :=
    (image_mono (fun _ h => h.1)).trans hq.image_eq.subset
  have hxy : {x} = ({y} : Set E) := by
    rw [← hA, ← hB, ← hbd]
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      exact ⟨hz, (hAB.subset ⟨hzA, hbdC hz⟩).1⟩
    · rintro ⟨hz, hzB⟩
      exact ⟨hz, (hAB.symm.subset ⟨hzB, hbdC hz⟩).1⟩
  exact singleton_injective hxy

end DifferentialGeometry.Topology.PiecewiseLinear
