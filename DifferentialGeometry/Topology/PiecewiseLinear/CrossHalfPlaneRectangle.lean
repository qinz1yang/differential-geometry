/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossQuarterLink
import DifferentialGeometry.Topology.PiecewiseLinear.BallPairArc
import DifferentialGeometry.Topology.PiecewiseLinear.CurvePrism

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

def crossHalfPlane (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  {p | ∃ a : ℝ, 0 ≤ a ∧ p.1 = a • fourSpokeModelLeaf i}

def crossHalfPlaneRectangle (r z : ℝ) (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) ×ˢ Icc (z - r) (z + r)

private theorem zero_ne_smul_leaf (i : Fin 4) {r : ℝ} (hr : 0 < r) :
    (0 : ℝ × ℝ) ≠ r • fourSpokeModelLeaf i := by
  exact (smul_ne_zero hr.ne' (fourSpokeModelLeaf_ne_zero i)).symm

theorem isPLBall_crossHalfPlaneRectangle (i : Fin 4) {r z : ℝ} (hr : 0 < r) :
    IsPLBall 2 (crossHalfPlaneRectangle r z i) :=
  isPLBall_two_prod (isPLBall_segment (zero_ne_smul_leaf i hr)) (isPLBall_Icc (by linarith))

open Classical in
theorem boundaryComplex_space_crossHalfPlaneRectangle (i : Fin 4) {r z : ℝ} (hr : 0 < r)
    (K : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) [Finite K.faces]
    [d : DecidableEq ((ℝ × ℝ) × ℝ)]
    (hK : K.space = crossHalfPlaneRectangle r z i) :
    (boundaryComplex 2 K).space =
      segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) ×ˢ {z - r, z + r} ∪
        ({0, r • fourSpokeModelLeaf i} : Set (ℝ × ℝ)) ×ˢ Icc (z - r) (z + r) := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq ((ℝ × ℝ) × ℝ) := Classical.decEq _
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  have hne := zero_ne_smul_leaf i hr
  let A := simplexComplex ({0, r • fourSpokeModelLeaf i} : Finset (ℝ × ℝ))
    (affineIndependent_coe_pair hne)
  let _ : Finite A.faces := (simplexComplex_faces_finite _ _).to_subtype
  have hAspace : A.space = segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) := by
    rw [simplexComplex_space _ _ (by simp), Finset.coe_pair, convexHull_pair]
  have hA : IsPLBall 1 A.space := hAspace.symm ▸ isPLBall_segment hne
  have hAb : (boundaryComplex 1 A).space = ({0, r • fourSpokeModelLeaf i} : Set (ℝ × ℝ)) := by
    change (boundaryComplex 1 (simplexComplex _ (affineIndependent_coe_pair hne))).space = _
    rw [boundaryComplex_simplexComplex (n := 0) (affineIndependent_coe_pair hne)
      (Finset.card_pair hne), simplexBoundary_pair_space hne]
  have hprod : K.space = A.space ×ˢ Icc (z - r) (z + r) := by
    rw [hAspace]
    exact hK
  rw [boundaryComplex_space_prism_one A hA (by linarith) K hprod, hAspace, hAb]

private theorem mem_scaled_arm_iff (i : Fin 4) {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) ↔
      ∃ a ∈ Icc (0 : ℝ) r, p = a • fourSpokeModelLeaf i := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * r, ⟨mul_nonneg ht.1 hr.le, ?_⟩, ?_⟩
    · nlinarith [ht.2]
    · simp only [smul_zero, zero_add, smul_smul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a / r, ⟨div_nonneg ha.1 hr.le, (div_le_one hr).mpr ha.2⟩, ?_⟩
    simp only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hr.ne']

theorem crossHalfPlaneRectangle_subset_closedBall (i : Fin 4) {r z : ℝ} (hr : 0 < r) :
    crossHalfPlaneRectangle r z i ⊆ closedBall ((0 : ℝ × ℝ), z) r := by
  rintro ⟨p, t⟩ ⟨hp, ht⟩
  obtain ⟨a, ha, rfl⟩ := (mem_scaled_arm_iff i hr).mp hp
  rw [mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right, Real.dist_eq]
  constructor
  · rw [norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg ha.1]
    exact ha.2
  · exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem mem_crossHalfPlaneRectangle_iff_of_mem_ball (i : Fin 4) {r z : ℝ} (hr : 0 < r)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ ball ((0 : ℝ × ℝ), z) r) :
    p ∈ crossHalfPlaneRectangle r z i ↔ p ∈ crossHalfPlane i := by
  have hp' := hp
  rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, Real.dist_eq] at hp'
  constructor
  · intro h
    obtain ⟨a, ha, heq⟩ := (mem_scaled_arm_iff i hr).mp h.1
    exact ⟨a, ha.1, heq⟩
  · rintro ⟨a, ha, heq⟩
    have har : a < r := by
      have h := hp'.1
      rw [heq, norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg ha] at h
      exact h
    exact ⟨(mem_scaled_arm_iff i hr).mpr ⟨a, ⟨ha, har.le⟩, heq⟩,
      ⟨by linarith [(abs_lt.mp hp'.2).1], by linarith [(abs_lt.mp hp'.2).2]⟩⟩

open Classical in
theorem mem_boundaryComplex_crossHalfPlaneRectangle_iff_of_mem_ball
    (i : Fin 4) {r z : ℝ} (hr : 0 < r)
    (K : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) [Finite K.faces]
    [d : DecidableEq ((ℝ × ℝ) × ℝ)]
    (hK : K.space = crossHalfPlaneRectangle r z i)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ ball ((0 : ℝ × ℝ), z) r) :
    p ∈ (boundaryComplex 2 K).space ↔ p.1 = 0 := by
  have hp' := hp
  rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, Real.dist_eq] at hp'
  have ht : p.2 ∈ Ioo (z - r) (z + r) :=
    ⟨by linarith [(abs_lt.mp hp'.2).1], by linarith [(abs_lt.mp hp'.2).2]⟩
  have hleaf : p.1 ≠ r • fourSpokeModelLeaf i := by
    intro heq
    have h := hp'.1
    rw [heq, norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg hr.le] at h
    exact lt_irrefl r h
  rw [boundaryComplex_space_crossHalfPlaneRectangle i hr K hK]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · rcases h with h | h
      · exact (ht.1.ne' h).elim
      · exact (ht.2.ne h).elim
    · exact h.resolve_right hleaf
  · intro h
    exact Or.inr ⟨Or.inl h, ht.1.le, ht.2.le⟩

theorem crossHalfPlaneRectangle_subset_crossHalfPlane (i : Fin 4) {r z : ℝ} (hr : 0 < r) :
    crossHalfPlaneRectangle r z i ⊆ crossHalfPlane i := by
  intro p hp
  obtain ⟨a, ha, heq⟩ := (mem_scaled_arm_iff i hr).mp hp.1
  exact ⟨a, ha.1, heq⟩

theorem crossHalfPlane_subset_crossPlanes (i : Fin 4) : crossHalfPlane i ⊆ crossPlanes := by
  rintro p ⟨a, -, heq⟩
  change p.1.1 = 0 ∨ p.1.2 = 0
  rw [heq]
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    simp [fourSpokeModelLeaf]

end DifferentialGeometry.Topology.PiecewiseLinear
