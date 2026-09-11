import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Exponential.Variation.Jacobi



open Bundle Manifold DifferentialGeometry Set Filter
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem diskMapConformalAt_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U V : ℂ → M} {z : ℂ}
    (h : U =ᶠ[𝓝 z] V) : DiskMapConformalAt g U z ↔ DiskMapConformalAt g V z := by
  unfold DiskMapConformalAt diskMapPartial
  erw [h.mfderiv_eq, h.eq_of_nhds]



theorem diskMapCovariantPartial_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U V : ℂ → M} {z : ℂ}
    (h : U =ᶠ[𝓝 z] V) (v w : ℂ) :
    (diskMapCovariantPartial g U z v w : E) = diskMapCovariantPartial g V z v w := by
  have hl : Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => z + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  apply DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
  · exact hl.eventually h
  · filter_upwards [hl.eventually (eventually_eventually_nhds.2 h)] with t ht
    have ht' : U =ᶠ[𝓝 (z + t • v)] V := ht
    exact congrArg (fun L => L w) (ht'.mfderiv_eq (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))


theorem diskMapTension_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U V : ℂ → M} {z : ℂ}
    (h : U =ᶠ[𝓝 z] V) : (diskMapTension g U z : E) = diskMapTension g V z := by
  unfold diskMapTension
  rw [diskMapCovariantPartial_congr_of_eventuallyEq g h,
    diskMapCovariantPartial_congr_of_eventuallyEq g h]
  rfl

end DifferentialGeometry.Geometry
