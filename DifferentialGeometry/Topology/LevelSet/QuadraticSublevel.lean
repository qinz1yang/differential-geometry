import DifferentialGeometry.Topology.Compactness.ExtremumNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set Metric

namespace OpenPartialHomeomorph

theorem exists_closedBall_image_sublevel_of_unique_minimum
    {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M] [CompactSpace M]
    (χ : OpenPartialHomeomorph E M) (hzero : (0 : E) ∈ χ.source)
    {f : M → ℝ} (hf : Continuous f) {α : ℝ} (hα : 0 < α)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = f (χ 0) + α / 2 * ‖y‖ ^ 2)
    (hmin : ∀ x, x ≠ χ 0 → f (χ 0) < f x) :
    ∃ R : ℝ, 0 < R ∧ closedBall 0 R ⊆ χ.source ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ R →
        χ '' closedBall 0 r = f ⁻¹' Iic (f (χ 0) + α / 2 * r ^ 2) ∧
        χ '' sphere 0 r = f ⁻¹' {f (χ 0) + α / 2 * r ^ 2} := by
  obtain ⟨δ, hδ, hδsource⟩ := Metric.mem_nhds_iff.mp (χ.open_source.mem_nhds hzero)
  obtain ⟨ε, hε, hlow⟩ := hf.exists_sublevel_subset_of_unique_minimum hmin
    χ.open_target (χ.map_source hzero)
  let R := min (δ / 2) (Real.sqrt (2 * ε / α))
  have hR : 0 < R := lt_min (half_pos hδ) (Real.sqrt_pos.mpr (by positivity))
  have hRsource : closedBall 0 R ⊆ χ.source :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hδ))).trans hδsource
  refine ⟨R, hR, hRsource, ?_⟩
  intro r hr hrR
  have hrsource : closedBall 0 r ⊆ χ.source := (closedBall_subset_closedBall hrR).trans hRsource
  have hheight : α / 2 * r ^ 2 ≤ ε := by
    have hrsqrt : r ≤ Real.sqrt (2 * ε / α) := hrR.trans (min_le_right _ _)
    have hrsq := (sq_le_sq₀ hr (Real.sqrt_nonneg _)).mpr hrsqrt
    rw [Real.sq_sqrt (by positivity)] at hrsq
    have hmul := (le_div_iff₀ hα).mp hrsq
    nlinarith
  have hsub : χ '' closedBall 0 r = f ⁻¹' Iic (f (χ 0) + α / 2 * r ^ 2) := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      change f (χ y) ≤ f (χ 0) + α / 2 * r ^ 2
      rw [hnormal y (hrsource hy)]
      have hyn : ‖y‖ ≤ r := mem_closedBall_zero_iff.mp hy
      have hmul : α / 2 * ‖y‖ ^ 2 ≤ α / 2 * r ^ 2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg y) hr).mpr hyn) (half_pos hα).le
      linarith
    · intro x hx
      have hxtarget : x ∈ χ.target := hlow (by
        change f x ≤ f (χ 0) + ε
        exact hx.trans (by linarith))
      refine ⟨χ.symm x, ?_, χ.right_inv hxtarget⟩
      rw [mem_closedBall_zero_iff]
      have hn := hnormal (χ.symm x) (χ.map_target hxtarget)
      rw [χ.right_inv hxtarget] at hn
      apply (sq_le_sq₀ (norm_nonneg _) hr).mp
      apply (mul_le_mul_iff_right₀ (half_pos hα)).mp
      change f x ≤ f (χ 0) + α / 2 * r ^ 2 at hx
      nlinarith
  refine ⟨hsub, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have hyn : ‖y‖ = r := mem_sphere_zero_iff_norm.mp hy
    change f (χ y) = f (χ 0) + α / 2 * r ^ 2
    rw [hnormal y (hrsource (sphere_subset_closedBall hy)), hyn]
  · intro x hx
    change f x = f (χ 0) + α / 2 * r ^ 2 at hx
    obtain ⟨y, hy, rfl⟩ := hsub.symm.subset hx.le
    refine ⟨y, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    apply (sq_eq_sq₀ (norm_nonneg y) hr).mp
    have hn := hnormal y (hrsource hy)
    nlinarith

theorem exists_closedBall_image_superlevel_of_unique_maximum
    {E M : Type*} [NormedAddCommGroup E] [TopologicalSpace M] [CompactSpace M]
    (χ : OpenPartialHomeomorph E M) (hzero : (0 : E) ∈ χ.source)
    {f : M → ℝ} (hf : Continuous f) {α : ℝ} (hα : α < 0)
    (hnormal : ∀ y ∈ χ.source, f (χ y) = f (χ 0) + α / 2 * ‖y‖ ^ 2)
    (hmax : ∀ x, x ≠ χ 0 → f x < f (χ 0)) :
    ∃ R : ℝ, 0 < R ∧ closedBall 0 R ⊆ χ.source ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ R →
        χ '' closedBall 0 r = f ⁻¹' Ici (f (χ 0) + α / 2 * r ^ 2) ∧
        χ '' sphere 0 r = f ⁻¹' {f (χ 0) + α / 2 * r ^ 2} := by
  obtain ⟨R, hR, hsource, hlevels⟩ := χ.exists_closedBall_image_sublevel_of_unique_minimum
    hzero hf.neg (neg_pos.mpr hα)
    (fun y hy => by simp only [Pi.neg_apply, hnormal y hy]; ring)
    (fun x hx => neg_lt_neg (hmax x hx))
  refine ⟨R, hR, hsource, ?_⟩
  intro r hr hrR
  obtain ⟨hsub, hlevel⟩ := hlevels r hr hrR
  refine ⟨hsub.trans ?_, hlevel.trans ?_⟩
  · ext x
    change -f x ≤ -f (χ 0) + -α / 2 * r ^ 2 ↔ f (χ 0) + α / 2 * r ^ 2 ≤ f x
    constructor <;> intro h <;> linarith
  · ext x
    change -f x = -f (χ 0) + -α / 2 * r ^ 2 ↔ f x = f (χ 0) + α / 2 * r ^ 2
    constructor <;> intro h <;> linarith

end OpenPartialHomeomorph
