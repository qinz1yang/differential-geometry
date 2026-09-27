import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Geometry.Riemannian (SectionalBoundedBelowAt
  ricci_lower_of_sectionalBoundedBelowAt)
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt
    (g : SmoothRiemannianMetric I M) (x : M) {δ : ℝ}
    (h : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ) :
    SectionalBoundedBelowAt g x (-δ) := by
  intro v w
  have hq := h 1 (fun _ => 1) (fun _ => v) (fun _ => w)
  simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
    Fin.sum_univ_one, one_mul, metricAlgebraicCurvatureTensorAt_coe] at hq
  change 0 ≤ metricRm04StandardAt g x v w w v + _ at hq
  rw [g.symm x w v] at hq
  nlinarith [hq]

theorem neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {δ : ℝ}
    (h : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ)
    (u : TangentSpace I x) :
    -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * δ) * g.inner x u u ≤ metricRicciAt g x (vec2 u u) := by
  rw [metricRicciAt_apply_eq_ricciTensor]
  have hric := ricci_lower_of_sectionalBoundedBelowAt g x
    (sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt g x h) u
  linarith

end DifferentialGeometry.Geometry.Curvature

end
