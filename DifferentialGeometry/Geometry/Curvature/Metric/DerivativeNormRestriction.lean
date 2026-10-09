import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormTensor
import DifferentialGeometry.Geometry.Curvature.EmbeddingCurvatureJets
import DifferentialGeometry.Geometry.Curvature.RicciRestriction

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : CompleteSpace F := FiniteDimensional.complete ℝ F

theorem curvatureDerivativeNorm_of_injective_local_isometry [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (k : ℕ) (x : M) :
    curvatureDerivativeNorm g k x = curvatureDerivativeNorm h k (f x) := by
  simpa only [curvatureDerivativeNorm, tensor0SFiberNorm,
    iteratedMetricCovariantDerivative_rm04_eq, iteratedCurvatureTensor_eq_iterCov] using
    curvature_jets_of_injective_local_isometry g h f hf hinj hmetric k x

theorem curvatureDerivativeNorm_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) (k : ℕ) (x : U) :
    curvatureDerivativeNorm (g.restrictOpen U) k x = curvatureDerivativeNorm g k (x : M) := by
  have hRm : metricRm04 (g.restrictOpen U) = restrictOpen0S 4 (V := U) (metricRm04 g) := by
    apply DFunLike.ext
    intro y
    apply tensor0SSpace_ext (I := I) 4 y
    intro slots
    change metricRm04 (g.restrictOpen U) y slots = metricRm04 g (y : M) slots
    simpa only [mfderiv_subtype_val_apply] using metricRm04_restrictOpen_eval g U y slots
  simp only [curvatureDerivativeNorm, tensor0SFiberNorm,
    iteratedMetricCovariantDerivative_rm04_eq, iteratedCurvatureTensor_eq_iterCov]
  rw [hRm, Geometry.Tensor.iter_cov_restrict_open]
  exact congrArg Real.sqrt (normSq0S_restrictOpen_apply g U (4 + k) x _)

end DifferentialGeometry.Geometry.Curvature
