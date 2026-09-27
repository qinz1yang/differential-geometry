import DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import DifferentialGeometry.Geometry.Metric.ParameterDerivative



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem contMDiffAt_metricFamilyQuadratic
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    (p : TangentBundle 𝓘(ℝ, E) M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2) (t, p) := by
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, E) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => q.2.proj) (t, p) :=
    (contMDiffAt_proj (IB := 𝓘(ℝ, E)) (TangentSpace 𝓘(ℝ, E))).comp (t, p) contMDiffAt_snd
  have hV : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E)))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => TotalSpace.mk' E q.2.proj q.2.2) (t, p) := by
    exact contMDiffAt_snd
  exact contMDiffAt_metricFamilySectionPairing hG contMDiffAt_fst hbase ht hV hV



theorem continuousAt_metricFamilyQuadratic_deriv
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    (p : TangentBundle 𝓘(ℝ, E) M) :
    ContinuousAt (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M =>
      deriv (fun r => (G r).inner q.2.proj q.2.2 q.2.2) q.1) (t, p) :=
  (contMDiffAt_deriv_fst (contMDiffAt_metricFamilyQuadratic hG ht p)).continuousAt

end DifferentialGeometry.Geometry
