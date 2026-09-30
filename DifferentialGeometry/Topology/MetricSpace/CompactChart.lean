import DifferentialGeometry.Topology.MetricSpace.LipschitzHomeomorph
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [ProperSpace Y]

theorem isCompact_of_bounded_bilipschitz_image {S : Set X} (hS : IsComplete S)
    {f : S → Y} {C K : ℝ≥0} (hLip : LipschitzWith C f) (hAnti : AntilipschitzWith K f)
    (hbounded : Bornology.IsBounded (range f)) : IsCompact S := by
  let := hS.completeSpace_coe
  have hc := isCompact_of_isClosed_isBounded (hAnti.isClosed_range hLip.uniformContinuous) hbounded
  apply isCompact_iff_isCompact_univ.mpr
  apply (hAnti.isEmbedding hLip.continuous).isCompact_iff.mpr
  simpa only [image_univ] using hc

theorem isCompact_closedBall_of_chart {q : X} {r s : ℝ} (hsr : s < r)
    (hs : IsComplete (closedBall q s)) {f : ball q r → Y} {C ε : ℝ≥0}
    (hε : 0 < ε) (hLip : LipschitzWith C f)
    (hlower : ∀ x y, (ε : ℝ) * dist x y ≤ dist (f x) (f y)) :
    IsCompact (closedBall q s) := by
  let g : closedBall q s → Y := fun x => f ⟨x, closedBall_subset_ball hsr x.property⟩
  have hgLip : LipschitzWith C g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hLip.dist_le_mul _ _
  have hgAnti : AntilipschitzWith ε⁻¹ g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    have h := hlower ⟨x, closedBall_subset_ball hsr x.property⟩
      ⟨y, closedBall_subset_ball hsr y.property⟩
    have he : (0 : ℝ) < ε := hε
    have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr he.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ he.ne', one_mul, NNReal.coe_inv, Subtype.dist_eq] using hh
  apply isCompact_of_bounded_bilipschitz_image hs hgLip hgAnti
  apply Metric.isBounded_iff.mpr
  refine ⟨(C : ℝ) * (2 * s), ?_⟩
  rintro u ⟨x, rfl⟩ v ⟨y, rfl⟩
  apply (hgLip.dist_le_mul x y).trans
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  change dist (x : X) (y : X) ≤ 2 * s
  have hx : dist (x : X) q ≤ s := x.property
  have hy : dist (y : X) q ≤ s := y.property
  have ht := dist_triangle (x : X) q (y : X)
  rw [dist_comm q (y : X)] at ht
  linarith

end Metric
