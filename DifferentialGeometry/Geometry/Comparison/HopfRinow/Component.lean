import DifferentialGeometry.Geometry.Metric.Completeness.ConnectedComponent
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

section

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem RiemannianMetricComplete.isCompact_intrinsicClosedBall_connectedComponent
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (p : M) (q : connectedComponentOpen (I := 𝓘(ℝ, E)) p) (r : ℝ) :
    IsCompact {x : connectedComponentOpen (I := 𝓘(ℝ, E)) p |
      riemannianEDistOf g (q : M) (x : M) ≤ ENNReal.ofReal r} := by
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) p
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let : SigmaCompactSpace C := sigmaCompactSpace_connectedComponent_of_riemannianMetric g p
  let : T2Space (TangentBundle 𝓘(ℝ, E) C) := inferInstance
  have hgC : RiemannianMetricComplete gC := hg.restrict_connectedComponent g p
  have hroot : DifferentialGeometry.RiemannianMetricComplete gC := hgC.to_canonical gC
  have hc := hroot.closedEBall_isCompact q r
  have heq : {x : C | riemannianEDistOf gC q x ≤ ENNReal.ofReal r} =
      {x : C | riemannianEDistOf g (q : M) (x : M) ≤ ENNReal.ofReal r} := by
    ext x
    exact (congrArg (fun d => d ≤ ENNReal.ofReal r)
      (Metric.edistOf_restrictOpen_connCompOpen g p q x)).to_iff
  rw [heq] at hc
  exact hc

end DifferentialGeometry.Geometry

end

end
