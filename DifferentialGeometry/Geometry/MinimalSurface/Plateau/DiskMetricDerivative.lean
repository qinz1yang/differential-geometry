import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import DifferentialGeometry.Geometry.Connection.SourceSectionPairing



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem fderiv_diskMapMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w x : ℂ) :
    fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q w) (diskMapPartial U q x)) z v =
      g.inner (U z) (diskMapCovariantPartial g U z v w) (diskMapPartial U z x) +
      g.inner (U z) (diskMapPartial U z w) (diskMapCovariantPartial g U z v x) := by
  exact fderiv_sourceSectionPairing g hs hU
    (contMDiffOn_source_partial hs hU (by simp) w)
    (contMDiffOn_source_partial hs hU (by simp) x) hz v




theorem fderiv_diskMapConformalCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    fderiv ℝ (diskMapConformalCoefficient g U) z v =
      2 * g.inner (U z) (diskMapCovariantPartial g U z v 1) (diskMapPartial U z 1) := by
  change fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)) z v = _
  rw [fderiv_diskMapMetricPairing g hs hU hz, g.symm (U z) (diskMapPartial U z 1)]
  ring

end DifferentialGeometry.Geometry
