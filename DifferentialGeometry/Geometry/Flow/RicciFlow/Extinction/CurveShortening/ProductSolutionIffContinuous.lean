import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveSmoothLift

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ProductCurve

omit [CompleteSpace E] in
theorem product_solution_iff_of_continuousOn_height
    (A : QuotientProductAtlas I M) [T2Space M] [I.Boundaryless]
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (c : ProductCurve M) {s u : ℝ} (hsu : s < u) {J : Set ℝ}
    (hJ : J = Ico s u ∨ J = Icc s u)
    (hyc : ContinuousOn (fun p : ℝ × ℝ => c.y p.1 p.2) (univ ×ˢ J))
    (hU : (c.unitTangent g lambda).SmoothOn (I := I) J) :
    letI := A.charts
    letI := A.smoothManifold
    c.IsSolutionOn g lambda J ↔
      c.map.IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) J :=
  c.product_solution_iff_of_frontiers A g lambda hlambda hsu hJ hyc hU

end ProductCurve

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
