import DifferentialGeometry.Geometry.Collapse.CurvatureScale

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem curvatureRadius_le_of_not_sectionalBoundedBelowAt
    (g : SmoothRiemannianMetric I M) {p q : M} {R : ℝ}
    (hR : 0 < R) (hq : riemannianEDistOf g p q ≤ ENNReal.ofReal R)
    (hsec : ¬ SectionalBoundedBelowAt g q (-(R ^ 2)⁻¹)) :
    curvatureRadius g p ≤ ENNReal.ofReal R := by
  unfold curvatureRadius
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun hcurv => ?_
  apply ENNReal.ofReal_le_ofReal
  by_contra! hlt
  have hqmem : q ∈ riemannianBallOf g p r :=
    hq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hlt)
  have hsquare : R ^ 2 ≤ r ^ 2 := by nlinarith
  exact hsec ((hcurv q hqmem).mono (neg_le_neg (inv_anti₀ (sq_pos_of_pos hR) hsquare)))

theorem sectionalBoundedBelowAt_of_lt_curvatureRadius
    (g : SmoothRiemannianMetric I M) {p q : M} {r : ℝ}
    (hr : ENNReal.ofReal r < curvatureRadius g p)
    (hq : q ∈ riemannianBallOf g p r) :
    SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹) := by
  have hrpos : 0 < r := ENNReal.ofReal_pos.mp (bot_le.trans_lt hq)
  by_contra hsec
  exact (not_lt_of_ge
    (curvatureRadius_le_of_not_sectionalBoundedBelowAt g hrpos hq.le hsec)) hr

end DifferentialGeometry.Geometry.Collapse
