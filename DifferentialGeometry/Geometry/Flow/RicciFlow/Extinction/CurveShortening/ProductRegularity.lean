import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCurveRegularityInput
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularityFrontier

noncomputable section
open Manifold
open DifferentialGeometry.Geometry.Curvature (RealTimeInterval)
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [CompactSpace M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}

theorem curve_shortening_local_regularity
    (B : RicciBackground (I := I) (M := M) D a b) (L₀ Θ₀ : ℝ) :
    CurveShorteningDerivativeEstimate B L₀ Θ₀ := by
  apply (curveShorteningDerivativeEstimate_iff_nonempty B L₀ Θ₀).mpr
  by_cases hL₀ : 0 ≤ L₀
  · by_cases hΘ₀ : 0 ≤ Θ₀
    · exact nonempty_curveShorteningRegularityInput B L₀ Θ₀ hL₀ hΘ₀
    · exact nonempty_curveShorteningRegularityInput_of_bound_neg B (Or.inr (lt_of_not_ge hΘ₀))
  · exact nonempty_curveShorteningRegularityInput_of_bound_neg B (Or.inl (lt_of_not_ge hL₀))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
