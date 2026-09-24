import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.SobolevExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveShortTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductWindowSmoothness

noncomputable section
open Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

theorem ProductCurve.localExistence_of_compact
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {D : RealTimeInterval} {a b : ℝ}
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ProductCurve.LocalExistence (I := I) (M := M) B lambda := by
  let A : QuotientProductAtlas I M := quotientProductAtlas (I := I) (M := M)
  let := A.charts
  let := A.smoothManifold
  obtain ⟨Bhat, _, hBhat, _⟩ :=
    exists_smoothMetricWindow_quotientProduct A B lambda hlambda
  exact ProductCurve.localExistence_of_quotientCurveLocalExistence
    (I := I) (M := M) A B lambda hlambda Bhat hBhat
      (curveShorteningLocalExistence_of_compact
        (I := I.prod 𝓘(ℝ, ℝ)) (M := M × Surgery.Topology.Circle) Bhat)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
end
