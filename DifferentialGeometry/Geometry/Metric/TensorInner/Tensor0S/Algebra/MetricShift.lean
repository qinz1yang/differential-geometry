import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normSq0S_sub_smul_metricTensor0S
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (a : ℝ) :
    normSq0S g x 2 (A - a • metricTensor0S g x) =
      normSq0S g x 2 A - 2 * a * metricTracePair0SAt g A +
        a ^ 2 * (Module.finrank ℝ E : ℝ) := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  have hinv : MetricInverseInBasis g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hmetric : normSq0S g x 2 (metricTensor0S g x) =
      (Module.finrank ℝ E : ℝ) := by
    change normSq0S g x 2 (metricTensor0S g x) =
      (Module.finrank ℝ (TangentSpace I x) : ℝ)
    simpa only [Fintype.card_fin] using
      normSq0S_metricTensor0S_eq_card g basis
        (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinv
  rw [_root_.Tensor0SBundle.normSq0S_sub,
    _root_.Tensor0SBundle.inner0S_smul_right,
    normSq0S_eq_inner (A := a • metricTensor0S g x), _root_.Tensor0SBundle.inner0S_smul_left,
    _root_.Tensor0SBundle.inner0S_smul_right, ← normSq0S_eq_inner, hmetric]
  rw [inner0S_symm g x A (metricTensor0S g x)]
  change _ = _
  dsimp only [metricTracePair0SAt]
  ring

end DifferentialGeometry.Tensor0SBundle
