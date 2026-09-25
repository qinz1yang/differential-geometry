import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.DerivativeENorm

set_option autoImplicit false
noncomputable section
open Set Function DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph
    (g h R : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) (j : ℕ) (x : M) :
    metricDerivNorm j (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph R f hf hinj) x =
      metricDerivNorm j g h R (f x) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : SigmaCompactSpace hf.image := by
    apply isSigmaCompact_univ_iff.mp
    have hs := isSigmaCompact_range (diffeomorphOntoImage f hf hinj).contMDiff.continuous
    have heq : Set.range (fun x => diffeomorphOntoImage f hf hinj x) = Set.univ :=
      Set.range_eq_univ.mpr (diffeomorphOntoImage f hf hinj).surjective
    rw [heq] at hs
    exact hs
  unfold pullbackMetricOfInjectiveLocalDiffeomorph
  rw [metricDerivNorm_pullbackCross, metricDerivNorm_restrictOpen]
  rw [diffeomorphOntoImage_apply]

theorem metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph
    (K : Set M) (k : ℕ) (g h R : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f) :
    metricDerivENormSupOn K k (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph R f hf hinj) =
      metricDerivENormSupOn (f '' K) k g h R := by
  simp only [metricDerivENormSupOn,
    metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph, iSup_image]

end DifferentialGeometry.Geometry.Metric
