/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningJunction
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import Mathlib.Topology.MetricSpace.Thickening

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Q" => (ℝ × ℝ) × ℝ

private def arcPlaneEmbedding (τ : ℝ) : (ℝ × ℝ) →ₗ[ℝ] Q where
  toFun z := ((z.1, 0), τ * z.2)
  map_add' := by intro x y; ext <;> simp [mul_add]
  map_smul' := by intro t x; ext <;> simp [mul_left_comm]

private theorem exists_rectangle_subset_of_axis_subset
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (haxis : {(0 : ℝ)} ×ˢ Icc (0 : ℝ) 1 ⊆ U) :
    ∃ δ > 0, Icc (-δ) δ ×ˢ Icc (-δ) (1 + δ) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_singleton.prod isCompact_Icc).exists_cthickening_subset_open hU haxis
  refine ⟨δ, hδ, fun z hz => hδU ?_⟩
  let t := max 0 (min 1 z.2)
  have ht0 : 0 ≤ t := le_max_left _ _
  have ht1 : t ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hdist : |z.2 - t| ≤ δ := by
    dsimp [t]
    rcases le_total z.2 0 with h | h
    · rw [min_eq_right (h.trans zero_le_one), max_eq_left h,
        sub_zero, abs_of_nonpos h]
      linarith [hz.2.1]
    · rw [max_eq_right (le_min zero_le_one h)]
      rcases le_total z.2 1 with h' | h'
      · rw [min_eq_right h', sub_self, abs_zero]
        exact hδ.le
      · rw [min_eq_left h', abs_of_nonneg (sub_nonneg.mpr h')]
        linarith [hz.2.2]
  apply mem_cthickening_of_dist_le z (0, t) δ ({(0 : ℝ)} ×ˢ Icc (0 : ℝ) 1)
    ⟨rfl, ht0, ht1⟩
  simp only [Prod.dist_eq, Real.dist_eq, sub_zero, max_le_iff]
  exact ⟨abs_le.mpr hz.1, hdist⟩

private theorem isPLHomeomorphOn_arcPlaneEmbedding {τ : ℝ} (hτ : τ ≠ 0)
    {R : Set (ℝ × ℝ)} (hR : IsPolyhedron R) :
    IsPLHomeomorphOn (arcPlaneEmbedding τ) R (arcPlaneEmbedding τ '' R) := by
  have hpl := isPiecewiseAffineOn_of_affine (arcPlaneEmbedding τ).toAffineMap isOpen_univ
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hR
    (hpl.mono_of_isPolyhedron hR (subset_univ _))
  apply InjOn.bijOn_image
  intro x _ y _ hxy
  exact Prod.ext (congrArg (fun p : Q => p.1.1) hxy)
    (mul_left_cancel₀ hτ (congrArg Prod.snd hxy))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_spheres_eq_on_charted_arc
    {S : Set E} {S' : Set F} (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    {Φ : Q → E} {Φ' : Q → F} {N N' : Set Q} {Ω : Set E} {Ω' : Set F}
    (hN : IsOpen N) (hN' : IsOpen N')
    (hΦ : IsPLHomeomorphOn Φ N Ω) (hΦ' : IsPLHomeomorphOn Φ' N' Ω')
    {τ τ' : ℝ} (hτ : 0 < τ) (hτ' : 0 < τ')
    (hcore : coreSegment τ ⊆ N) (hcore' : coreSegment τ' ⊆ N')
    (hplane : ∀ p ∈ N, p.1.2 = 0 → Φ p ∈ S)
    (hplane' : ∀ p ∈ N', p.1.2 = 0 → Φ' p ∈ S') :
    ∃ b : E → F, IsPLHomeomorphOn b S S' ∧
      b '' (Φ '' coreSegment τ) = Φ' '' coreSegment τ' ∧
      b (Φ 0) = Φ' 0 ∧ b (Φ ((0, 0), τ)) = Φ' ((0, 0), τ') ∧
      ∀ t ∈ Icc (0 : ℝ) 1, b (Φ ((0, 0), τ * t)) = Φ' ((0, 0), τ' * t) := by
  classical
  let e := arcPlaneEmbedding τ
  let e' := arcPlaneEmbedding τ'
  have hec : Continuous e := (arcPlaneEmbedding τ).continuous_of_finiteDimensional
  have hec' : Continuous e' := (arcPlaneEmbedding τ').continuous_of_finiteDimensional
  have hNaxis : {(0 : ℝ)} ×ˢ Icc (0 : ℝ) 1 ⊆ e ⁻¹' N ∩ e' ⁻¹' N' := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hx0 : x = 0 := hx
    subst x
    constructor
    · exact hcore ⟨rfl, mul_nonneg hτ.le ht.1,
        (mul_le_mul_of_nonneg_left ht.2 hτ.le).trans_eq (mul_one τ)⟩
    · exact hcore' ⟨rfl, mul_nonneg hτ'.le ht.1,
        (mul_le_mul_of_nonneg_left ht.2 hτ'.le).trans_eq (mul_one τ')⟩
  obtain ⟨δ, hδ, hRN⟩ := exists_rectangle_subset_of_axis_subset
    ((hN.preimage hec).inter (hN'.preimage hec')) hNaxis
  let R := Icc (-δ) δ ×ˢ Icc (-δ) (1 + δ)
  have hR : IsPLBall 2 R := isPLBall_two_prod (isPLBall_Icc (by linarith))
    (isPLBall_Icc (by linarith))
  have he : IsPLHomeomorphOn e R (e '' R) :=
    isPLHomeomorphOn_arcPlaneEmbedding hτ.ne' hR.isPolyhedron
  have he' : IsPLHomeomorphOn e' R (e' '' R) :=
    isPLHomeomorphOn_arcPlaneEmbedding hτ'.ne' hR.isPolyhedron
  have heN : e '' R ⊆ N := fun _ ⟨z, hz, hzy⟩ => hzy ▸ (hRN hz).1
  have heN' : e' '' R ⊆ N' := fun _ ⟨z, hz, hzy⟩ => hzy ▸ (hRN hz).2
  let g := Φ ∘ e
  let g' := Φ' ∘ e'
  let D := g '' R
  let D' := g' '' R
  have hg : IsPLHomeomorphOn g R D := by
    simpa only [g, D, image_comp] using he.trans
      (hΦ.restrict (hR.of_isPLHomeomorphOn he).isPolyhedron heN)
  have hg' : IsPLHomeomorphOn g' R D' := by
    simpa only [g', D', image_comp] using he'.trans
      (hΦ'.restrict (hR.of_isPLHomeomorphOn he').isPolyhedron heN')
  have hDS : D ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    exact hplane (e z) (heN ⟨z, hz, rfl⟩) rfl
  have hDS' : D' ⊆ S' := by
    rintro _ ⟨z, hz, rfl⟩
    exact hplane' (e' z) (heN' ⟨z, hz, rfl⟩) rfl
  let f := g' ∘ Function.invFunOn g R
  have hf : IsPLHomeomorphOn f D D' := hg.symm.trans hg'
  obtain ⟨b, hb, hbf⟩ := exists_isPLHomeomorphOn_eqOn_disk_of_isPLSphere_two
    hS hS' (hR.of_isPLHomeomorphOn hg) hDS hf hDS'
  have haxisR : ∀ t ∈ Icc (0 : ℝ) 1, (0, t) ∈ R := by
    intro t ht
    exact ⟨⟨by linarith, hδ.le⟩, by constructor <;> linarith [ht.1, ht.2]⟩
  have haxis : ∀ t ∈ Icc (0 : ℝ) 1,
      b (Φ ((0, 0), τ * t)) = Φ' ((0, 0), τ' * t) := by
    intro t ht
    change b (g (0, t)) = g' (0, t)
    rw [hbf (hg.bijOn.mapsTo (haxisR t ht))]
    change g' (Function.invFunOn g R (g (0, t))) = g' (0, t)
    rw [hg.bijOn.invOn_invFunOn.1 (haxisR t ht)]
  have hcoreimg (a : ℝ) (ha : 0 < a) :
      coreSegment a = (fun t : ℝ => ((0, 0), a * t)) '' Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · intro p hp
      refine ⟨p.2 / a, ⟨div_nonneg hp.2.1 ha.le, (div_le_one ha).mpr hp.2.2⟩, ?_⟩
      apply Prod.ext
      · exact hp.1.symm
      · exact mul_div_cancel₀ _ ha.ne'
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨rfl, mul_nonneg ha.le ht.1,
        (mul_le_mul_of_nonneg_left ht.2 ha.le).trans_eq (mul_one a)⟩
  refine ⟨b, hb, ?_, ?_, ?_, haxis⟩
  · rw [hcoreimg τ hτ, hcoreimg τ' hτ', image_image, image_image, image_image]
    exact image_congr haxis
  · simpa only [mul_zero, Prod.mk_zero_zero] using haxis 0 (by norm_num)
  · simpa only [mul_one] using haxis 1 (by norm_num)

end DifferentialGeometry.Topology.PiecewiseLinear
