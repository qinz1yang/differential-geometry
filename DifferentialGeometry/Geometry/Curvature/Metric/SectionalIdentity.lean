/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ayush Khaitan, DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricRm04StandardAt_eq_of_sectionalCurvature_eq
    (g : SmoothRiemannianMetric I M) (K : ℝ) (p : M)
    (hg : ∀ v w : TangentSpace I p,
      LinearIndependent ℝ ![v, w] → Riemannian.sectionalCurvature g p v w = K)
    (v w : TangentSpace I p) :
    metricRm04StandardAt g p v w w v =
      K * (g.inner p v v * g.inner p w w - g.inner p v w * g.inner p v w) := by
  by_cases hvw : LinearIndependent ℝ ![v, w]
  · have hd := Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g p v w hvw
    have hk := hg v w hvw
    rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div] at hk
    have hd' : g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2 ≠ 0 := by
      simpa only [Riemannian.sectionalCurvatureDenominator_def] using ne_of_gt hd
    simpa only [pow_two] using (div_eq_iff hd').mp hk
  · rw [Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent g p v w hvw]
    have hd : Riemannian.sectionalCurvatureDenominator g p v w = 0 := by
      apply le_antisymm _ (Riemannian.sectionalCurvatureDenominator_nonneg g p v w)
      apply le_of_not_gt
      intro hpos
      exact hvw (Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
        g p v w hpos)
    rw [Riemannian.sectionalCurvatureDenominator_def, pow_two] at hd
    rw [hd, mul_zero]

end DifferentialGeometry.Geometry.Curvature
