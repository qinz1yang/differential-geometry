import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatSectors

/-!
# The flat triangle is covered by the main set and the vertex discs

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§1 condition S4 and §3, with review 27's certificate). Every point of the triangle other than the
outer vertex lies in the main set or in one of the three vertex discs
(`triangle_diff_subset_cover`): interior points are in the open triangle, wall points close to a
vertex are in its disc (the patch margin is below `rⱼ sin θⱼ`), the other wall points are in the
patch of their wall (wall images, wedges on the walls; `mem_cover_of_wallOne`,
`mem_cover_of_wallZero`, `mem_cover_of_wallTwo`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

theorem ofReal_mem_wedgeSet {x a : ℝ} (hx : 0 < x) (ha : 0 < a) : (x : ℂ) ∈ wedgeSet a :=
  ⟨by exact_mod_cast hx.ne', by rw [arg_ofReal_of_nonneg hx.le, abs_zero]; exact ha⟩

omit D in
theorem rotOne_smul_vertexOne (t : ℝ) :
    σ.rotOne ((t : ℂ) * σ.vertexOne) = (((1 - t) * Real.sin σ.θ₂ : ℝ) : ℂ) := by
  rw [EuclidShape.rotOne, EuclidShape.vertexOne]
  have e : exp (-((σ.θ₃ : ℂ) * I)) * exp ((σ.θ₃ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [ofReal_mul, ofReal_sub, ofReal_one]
  linear_combination (((1 : ℂ) - t) * ((Real.sin σ.θ₂ : ℝ) : ℂ)) * e

omit D in
theorem rot_smul_vertexOne (t : ℝ) :
    exp (-((σ.θ₃ : ℂ) * I)) * ((t : ℂ) * σ.vertexOne) = ((t * Real.sin σ.θ₂ : ℝ) : ℂ) := by
  rw [EuclidShape.vertexOne]
  have e : exp (-((σ.θ₃ : ℂ) * I)) * exp ((σ.θ₃ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [ofReal_mul]
  linear_combination ((t : ℂ) * ((Real.sin σ.θ₂ : ℝ) : ℂ)) * e

omit D in
theorem rotTwo_smul_vertexTwo (t : ℝ) :
    exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo ((t : ℂ) * σ.vertexTwo) =
      (((1 - t) * Real.sin σ.θ₁ : ℝ) : ℂ) := by
  rw [EuclidShape.rotTwo, EuclidShape.vertexTwo]
  have e : exp (-((σ.θ₂ : ℂ) * I)) * exp ((σ.θ₂ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [ofReal_mul, ofReal_sub, ofReal_one]
  linear_combination (((1 : ℂ) - t) * ((Real.sin σ.θ₁ : ℝ) : ℂ)) * e

omit D in
theorem rotTwo_segTwo (t : ℝ) :
    σ.rotTwo (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) =
      ((t * Real.sin σ.θ₃ : ℝ) : ℂ) := by
  rw [EuclidShape.rotTwo, add_sub_cancel_left, ← neg_sub σ.vertexTwo σ.vertexOne,
    σ.vertexTwo_sub_vertexOne]
  have e : exp ((σ.θ₂ : ℂ) * I) * exp (-((σ.θ₂ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [ofReal_mul]
  linear_combination ((t : ℂ) * ((Real.sin σ.θ₃ : ℝ) : ℂ)) * e

omit D in
theorem rot_rotOne_segTwo (t : ℝ) :
    exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) =
      (((1 - t) * Real.sin σ.θ₃ : ℝ) : ℂ) := by
  have hz : σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo) =
      σ.vertexOne + ((1 - t : ℝ) : ℂ) * (σ.vertexTwo - σ.vertexOne) := by push_cast; ring
  rw [hz, rotOne_segOne]
  have e : exp (-((σ.θ₁ : ℂ) * I)) * exp ((σ.θ₁ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination ((((1 - t) * Real.sin σ.θ₃ : ℝ)) : ℂ) * e

theorem kap_lt_mul {r s : ℝ} (hr : 0 < r) (hrr : r = radOne D ∨ r = radTwo D ∨ r = radThree D)
    (hs0 : 0 < s) (hs : sProd σ ≤ s) : kap D < r * s := by
  have := kap_le_of D hr hrr hs
  nlinarith [mul_pos hr hs0]

theorem mem_cover_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0)
    (h0 : z ≠ 0) : z ∈ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  by_cases h1 : z = σ.vertexOne
  · left; left; right
    change ‖z - σ.vertexOne‖ < radOne D
    rw [h1, sub_self, norm_zero]; exact radOne_pos D
  obtain ⟨hzb, n0, n1⟩ := eq_smul_vertexOne_of_wallOne hz hw
  set t := σ.baryOne z with ht
  obtain ⟨e0, e1, e2⟩ := wallSide_smul_vertexOne (σ := σ) t
  rw [← hzb] at e0 e1 e2
  have s1 := σ.sin_θ₁_pos
  have s2 := σ.sin_θ₂_pos
  have s3 := σ.sin_θ₃_pos
  by_cases hk0 : σ.wallSide 0 z ≤ kap D
  · right
    change ‖z‖ < radThree D
    rw [hzb, norm_mul, Complex.norm_real, Real.norm_of_nonneg n0, σ.norm_vertexOne]
    have := kap_lt_mul D (radThree_pos D) (Or.inr (Or.inr rfl)) s3 sProd_le_sin3
    rw [e0] at hk0
    nlinarith
  by_cases hk2 : σ.wallSide 2 z ≤ kap D
  · left; left; right
    change ‖z - σ.vertexOne‖ < radOne D
    rw [hzb, show ((t : ℂ) * σ.vertexOne - σ.vertexOne) = -(((1 - t : ℝ) : ℂ) * σ.vertexOne) by
      push_cast; ring, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      σ.norm_vertexOne]
    have := kap_lt_mul D (radOne_pos D) (Or.inl rfl) s1 sProd_le_sin1
    rw [e2] at hk2
    nlinarith
  left; left; left; left; right
  simp only [not_le] at hk0 hk2
  have hr : σ.refl 1 z = z := σ.refl_of_wallSide_eq_zero hw
  have ht0 : 0 < t := lt_of_le_of_ne n0 (fun h => h0 (by rw [hzb, ← h, ofReal_zero, zero_mul]))
  have ht1 : t < 1 := lt_of_le_of_ne n1 (fun h => h1 (by rw [hzb, h, ofReal_one, one_mul]))
  refine ⟨foldWall_diff_subset_V' D 1 ⟨⟨hz, hw⟩, h0⟩, hk0, hk2, by rwa [hr], by rwa [hr],
    (re_f_wallOne D hz hw h0 h1).1, Or.inr ?_, Or.inr ?_⟩
  · rw [hzb, rotOne_smul_vertexOne]
    exact ofReal_mem_wedgeSet (by nlinarith) (by linarith [σ.θ₁_pos])
  · rw [hzb, rot_smul_vertexOne]
    exact ofReal_mem_wedgeSet (by nlinarith) (by linarith [σ.θ₃_pos])

theorem mem_cover_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0)
    (h0 : z ≠ 0) : z ∈ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  by_cases h2 : z = σ.vertexTwo
  · left; right
    change ‖z - σ.vertexTwo‖ < radTwo D
    rw [h2, sub_self, norm_zero]; exact radTwo_pos D
  obtain ⟨hzb, n0, n1⟩ := eq_smul_vertexTwo_of_wallZero hz hw
  set t := σ.baryTwo z with ht
  obtain ⟨e0, e1, e2⟩ := wallSide_smul_vertexTwo (σ := σ) t
  rw [← hzb] at e0 e1 e2
  have s1 := σ.sin_θ₁_pos
  have s2 := σ.sin_θ₂_pos
  have s3 := σ.sin_θ₃_pos
  by_cases hk1 : σ.wallSide 1 z ≤ kap D
  · right
    change ‖z‖ < radThree D
    rw [hzb, norm_mul, Complex.norm_real, Real.norm_of_nonneg n0, σ.norm_vertexTwo]
    have := kap_lt_mul D (radThree_pos D) (Or.inr (Or.inr rfl)) s3 sProd_le_sin3
    rw [e1] at hk1
    nlinarith
  by_cases hk2 : σ.wallSide 2 z ≤ kap D
  · left; right
    change ‖z - σ.vertexTwo‖ < radTwo D
    rw [hzb, show ((t : ℂ) * σ.vertexTwo - σ.vertexTwo) = -(((1 - t : ℝ) : ℂ) * σ.vertexTwo) by
      push_cast; ring, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      σ.norm_vertexTwo]
    have := kap_lt_mul D (radTwo_pos D) (Or.inr (Or.inl rfl)) s2 sProd_le_sin2
    rw [e2] at hk2
    nlinarith
  left; left; left; left; left; right
  simp only [not_le] at hk1 hk2
  have hr : σ.refl 0 z = z := σ.refl_of_wallSide_eq_zero hw
  have ht0 : 0 < t := lt_of_le_of_ne n0 (fun h => h0 (by rw [hzb, ← h, ofReal_zero, zero_mul]))
  have ht1 : t < 1 := lt_of_le_of_ne n1 (fun h => h2 (by rw [hzb, h, ofReal_one, one_mul]))
  refine ⟨foldWall_diff_subset_V' D 0 ⟨⟨hz, hw⟩, h0⟩, hk1, hk2, by rwa [hr], by rwa [hr],
    (re_f_wallZero D hz hw h0 h2).2, Or.inr ?_, Or.inr ?_⟩
  · rw [hzb, rotTwo_smul_vertexTwo]
    exact ofReal_mem_wedgeSet (by nlinarith) (by linarith [σ.θ₂_pos])
  · rw [hzb, EuclidShape.vertexTwo, ← ofReal_mul]
    exact ofReal_mem_wedgeSet (by nlinarith) (by linarith [σ.θ₃_pos])

theorem mem_cover_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0)
    (h0 : z ≠ 0) : z ∈ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  by_cases h1 : z = σ.vertexOne
  · left; left; right
    change ‖z - σ.vertexOne‖ < radOne D
    rw [h1, sub_self, norm_zero]; exact radOne_pos D
  by_cases h2 : z = σ.vertexTwo
  · left; right
    change ‖z - σ.vertexTwo‖ < radTwo D
    rw [h2, sub_self, norm_zero]; exact radTwo_pos D
  obtain ⟨hzb, n0, n1⟩ := eq_seg_of_wallTwo hz hw
  set t := σ.baryOne z with ht
  obtain ⟨e0, e1, e2⟩ := wallSide_segTwo (σ := σ) t
  rw [← hzb] at e0 e1 e2
  have s1 := σ.sin_θ₁_pos
  have s2 := σ.sin_θ₂_pos
  have s3 := σ.sin_θ₃_pos
  have hn12 : ‖σ.vertexOne - σ.vertexTwo‖ = Real.sin σ.θ₃ := σ.norm_vertexOne_sub_vertexTwo
  by_cases hk0 : σ.wallSide 0 z ≤ kap D
  · left; right
    change ‖z - σ.vertexTwo‖ < radTwo D
    rw [hzb, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg n0, hn12]
    have := kap_lt_mul D (radTwo_pos D) (Or.inr (Or.inl rfl)) s2 sProd_le_sin2
    rw [e0] at hk0
    nlinarith
  by_cases hk1 : σ.wallSide 1 z ≤ kap D
  · left; left; right
    change ‖z - σ.vertexOne‖ < radOne D
    rw [hzb, show σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo) - σ.vertexOne =
      -(((1 - t : ℝ) : ℂ) * (σ.vertexOne - σ.vertexTwo)) by push_cast; ring, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (by linarith), hn12]
    have := kap_lt_mul D (radOne_pos D) (Or.inl rfl) s1 sProd_le_sin1
    rw [e1] at hk1
    nlinarith
  left; left; left; right
  simp only [not_le] at hk0 hk1
  have hr : σ.refl 2 z = z := σ.refl_of_wallSide_eq_zero hw
  have ht0 : 0 < t := lt_of_le_of_ne n0 (fun h => h2 (by
    rw [hzb, ← h, ofReal_zero, zero_mul, add_zero]))
  have ht1 : t < 1 := lt_of_le_of_ne n1 (fun h => h1 (by rw [hzb, h, ofReal_one, one_mul]; ring))
  have hre := re_f_wallTwo D hz hw h1 h2
  have him := im_f_of_wall D hz hw h0
  refine ⟨foldWall_diff_subset_V' D 2 ⟨⟨hz, hw⟩, h0⟩, hk0, hk1, by rwa [hr], by rwa [hr],
    hre.1, hre.2, ?_, Or.inr ?_, Or.inr ?_⟩
  · rw [normSq_apply, him, mul_zero, add_zero]
    nlinarith [hre.1, hre.2]
  · rw [hzb, rot_rotOne_segTwo]
    exact ofReal_mem_wedgeSet (by nlinarith) (by linarith [σ.θ₁_pos])
  · rw [hzb, rotTwo_segTwo]
    exact ofReal_mem_wedgeSet (by nlinarith) (by linarith [σ.θ₂_pos])

theorem triangle_diff_subset_cover :
    σ.triangle \ {0} ⊆ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  rintro z ⟨hz, h0⟩
  have h0' : z ≠ 0 := h0
  by_cases hi : ∀ i, 0 < σ.wallSide i z
  · left; left; left; left; left; left; exact hi
  simp only [not_forall, not_lt] at hi
  obtain ⟨i, hi⟩ := hi
  have hw : σ.wallSide i z = 0 := le_antisymm hi (hz i)
  fin_cases i
  · exact mem_cover_of_wallZero D hz hw h0'
  · exact mem_cover_of_wallOne D hz hw h0'
  · exact mem_cover_of_wallTwo D hz hw h0'

end ClosedTriangle

end GC.Seifert
