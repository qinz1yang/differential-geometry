import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

/-!
# Curvature radius upper bounds from a sectional curvature bound (S-HG-INTAKE-2, suffix `_HGI2`)

Verbatim extension of the tracked `Geometry/Collapse/CurvatureRadiusBounds.lean`: the section of the
donor file (branch `codex/della-mostow-smooth-adapter-20261004`, 467465bc6c) that the tracked file
does not have, namely `curvatureRadius_le_of_metricRm04StandardAt_le` and
`curvatureRadius_le_of_sectionalCurvature_le`.  The donor's `CurvatureRadiusConvergence` (see
`CurvatureRadiusConvergencePortHGI2`) uses them.  The tracked file is not edited; if it is
upgraded to the donor version, this file is retired.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section

open DifferentialGeometry.Geometry.Curvature

theorem curvatureRadius_le_of_metricRm04StandardAt_le
    (g : SmoothRiemannianMetric I M) {p q : M} {R : ℝ}
    (hR : 0 < R) (hq : riemannianEDistOf g p q ≤ ENNReal.ofReal R)
    (v w : TangentSpace I q)
    (hvw : 0 < sectionalCurvatureDenominator g q v w)
    (hsec : metricRm04StandardAt g q v w w v ≤
      -(R ^ 2)⁻¹ * sectionalCurvatureDenominator g q v w) :
    curvatureRadius g p ≤ ENNReal.ofReal R := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεpos : 0 < (ε : ℝ) := hε
  have hR' : 0 < R + (ε : ℝ) := add_pos hR hεpos
  have hRR' : R < R + (ε : ℝ) := lt_add_of_pos_right _ hεpos
  have hsquare : R ^ 2 < (R + (ε : ℝ)) ^ 2 :=
    (sq_lt_sq₀ hR.le hR'.le).mpr hRR'
  have hinv : ((R + (ε : ℝ)) ^ 2)⁻¹ < (R ^ 2)⁻¹ :=
    inv_strictAnti₀ (sq_pos_of_pos hR) hsquare
  have hstrict : metricRm04StandardAt g q v w w v <
      -((R + (ε : ℝ)) ^ 2)⁻¹ * sectionalCurvatureDenominator g q v w :=
    hsec.trans_lt (mul_lt_mul_of_pos_right (neg_lt_neg hinv) hvw)
  have hnot : ¬ SectionalBoundedBelowAt g q (-((R + (ε : ℝ)) ^ 2)⁻¹) := by
    intro h
    exact (not_lt_of_ge (h v w)) hstrict
  have hbound := curvatureRadius_le_of_not_sectionalBoundedBelowAt g hR'
    (hq.trans (ENNReal.ofReal_le_ofReal hRR'.le)) hnot
  simpa only [ENNReal.ofReal_add hR.le ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    using hbound

theorem curvatureRadius_le_of_sectionalCurvature_le [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {p q : M} {R : ℝ}
    (hR : 0 < R) (hq : riemannianEDistOf g p q ≤ ENNReal.ofReal R)
    (v w : TangentSpace I q) (hvw : LinearIndependent ℝ ![v, w])
    (hsec : sectionalCurvature g q v w ≤ -(R ^ 2)⁻¹) :
    curvatureRadius g p ≤ ENNReal.ofReal R := by
  have hden := sectionalCurvatureDenominator_pos_of_linearIndependent g q v w hvw
  apply curvatureRadius_le_of_metricRm04StandardAt_le g hR hq v w hden
  rw [sectionalCurvature_eq_metricRm04StandardAt_div] at hsec
  exact (div_le_iff₀ hden).mp hsec

end

end DifferentialGeometry.Geometry.Collapse
