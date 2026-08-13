import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.LeviCivita
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.MLieBracket
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PullbackConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
theorem riemann_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)
      = pullback_connection_construct g Φ := rfl

end DifferentialGeometry.PDE.RicciFlow.Pullback
