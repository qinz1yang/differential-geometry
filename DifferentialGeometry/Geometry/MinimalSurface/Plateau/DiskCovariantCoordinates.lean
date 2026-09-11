import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricDerivative
import DifferentialGeometry.Geometry.Connection.SourceCovariantPartial






noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem diskMapCovariantPartial_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    let F := (extChartAt 𝓘(ℝ, E) (U z)) ∘ U
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ (U z)
        (diskMapCovariantPartial g U z v w) =
      fderiv ℝ (fun q => fderiv ℝ F q w) z v +
        chartChristoffelContraction g (U z) (fderiv ℝ F z v) (fderiv ℝ F z w) (F z) :=
  sourceCovariantPartial_chart g hs hU hz v w



theorem diskMapCovariantPartial_symm
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    diskMapCovariantPartial g U z v w = diskMapCovariantPartial g U z w v :=
  sourceCovariantPartial_symm g hs hU hz v w

end DifferentialGeometry.Geometry
