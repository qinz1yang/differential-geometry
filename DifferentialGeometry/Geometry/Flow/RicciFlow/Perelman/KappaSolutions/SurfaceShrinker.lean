import DifferentialGeometry.Geometry.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Metric.Completeness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem complete_surface_shrinker_compact_constant_scalar
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (hdim : Module.finrank ℝ E = 2)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsoliton : isGradientRicciSoliton (I := I) g f sigma)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0) :
    CompactSpace M ∧ ∀ x : M, metricScalarAt (I := I) g x = sigma := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
