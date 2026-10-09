import DifferentialGeometry.Geometry.Metric.ActualCloudContributorLocality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Consumer of CFS28 on explicit data in `ℝ²`: blocks `span{e₀}` (`R = 1`, the full reference marker) and
`span{e₁}` (`R = 1/100 < ρ/16`), the actual image `e₀` at scale `ρ = 1`, `b = 1`, `Σ = 1/640`, and the tilted model
direction `e₀ + e₁`. CFS28's scale chain (AM) forces the deletion of the small block: the contributing centre has
zero `e₁` coordinate and the pruned plane loses the NONZERO `e₁` component of the model direction. -/

set_option autoImplicit false
noncomputable section
open Set Metric

namespace GC.MetricGeometry

/-- The coordinate functionals `⟪e_j, ·⟫` of `ℝ²` are 1-Lipschitz. -/
theorem actualCloud_coordinate_lipschitz (j : Fin 2) :
    LipschitzWith 1 (fun z : EuclideanSpace ℝ (Fin 2) =>
      innerSL ℝ (EuclideanSpace.single j (1 : ℝ)) z) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [Real.dist_eq, ← map_sub, dist_eq_norm, NNReal.coe_one, one_mul, innerSL_apply_apply]
  calc |inner ℝ (EuclideanSpace.single j (1 : ℝ)) (z - w)|
      ≤ ‖EuclideanSpace.single j (1 : ℝ)‖ * ‖z - w‖ := abs_real_inner_le_norm _ _
    _ = ‖z - w‖ := by rw [PiLp.norm_single, norm_one, one_mul]

/-- CFS28 consumer: deletion of the small block at the contributing centre and on its pruned plane. -/
theorem actualCloud_contributor_locality_consumer :
    let e : Fin 2 → EuclideanSpace ℝ (Fin 2) := fun j => EuclideanSpace.single j 1
    let V : Fin 2 → Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := fun j => ℝ ∙ e j
    let R : Fin 2 → ℝ := ![1, 1 / 100]
    (V 1).starProjection (e 0) = 0 ∧ (e 0 + e 1) 1 ≠ 0 ∧
      actualCloudPrunedProjection V R 0 (e 0 + e 1) 1 = 0 := by
  intro e V R
  let coord : Fin 2 → EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := fun j => innerSL ℝ (e j)
  have hcoord : ∀ j y, coord j y = y j := by
    intro j y
    simp only [coord, e, innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
  have hR0 : R 0 = 1 := rfl
  have hR1 : R 1 = 1 / 100 := rfl
  have he00 : e 0 0 = 1 := by simp [e]
  have he01 : e 0 1 = 0 := by simp [e]
  have hproj_zero : ∀ (j : Fin 2) (y : EuclideanSpace ℝ (Fin 2)), y j = 0 →
      (V j).starProjection y = 0 := by
    intro j y hy
    apply ((V j).starProjection_apply_eq_zero_iff).mpr
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← innerSL_apply_apply (𝕜 := ℝ)]
    change coord j y = 0
    rw [hcoord, hy]
  have hmeet : (closedBall (e 0) (80 * 1 * ((1 / 640 : ℝ) * 1)) ∩
      ball (e 0) (8 * 1 * ((1 / 640 : ℝ) * 1))).Nonempty :=
    ⟨e 0, mem_closedBall_self (by norm_num), mem_ball_self (by norm_num)⟩
  have hres := actualCloud_contributor_marker_locality (M := Unit) (E := ℝ)
    (fun _ => e 0) (fun _ => 1) V (fun j z => coord j z) R
    (by intro j; fin_cases j <;> simp [R])
    (fun j => actualCloud_coordinate_lipschitz j)
    (fun _ => ⟨0, by rw [hcoord, he00, hR0]⟩)
    (by intro j q; fin_cases j <;> simp [hcoord, he00, he01])
    (by
      intro j q hpos
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, hR0]; norm_num
      · simp only [Fin.mk_one, Fin.isValue, hcoord, he01] at hpos
        exact absurd hpos (lt_irrefl 0))
    (by
      intro j q hzero
      exact hproj_zero j (e 0) (by rw [← hcoord]; exact hzero))
    (b := 1) (σ := 1 / 640) le_rfl (by norm_num) (by norm_num)
    (fun _ => ()) (fun _ => ()) (fun _ => 0)
    (fun _ => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (e 0 + e 1))
    () (e 0) rfl rfl (e 0) rfl rfl (by rw [hcoord, he00, hR0]) hmeet 1
    (by rw [hR1]; norm_num)
  obtain ⟨hcentre, hplane⟩ := hres
  have hmem : actualCloudPrunedProjection V R 0 (e 0 + e 1) ∈ (V 1)ᗮ := by
    apply hplane
    exact ⟨(1 : ℝ), by simp⟩
  refine ⟨hcentre, by simp [e], ?_⟩
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← innerSL_apply_apply (𝕜 := ℝ)] at hmem
  change coord 1 (actualCloudPrunedProjection V R 0 (e 0 + e 1)) = 0 at hmem
  rwa [hcoord] at hmem

end GC.MetricGeometry
