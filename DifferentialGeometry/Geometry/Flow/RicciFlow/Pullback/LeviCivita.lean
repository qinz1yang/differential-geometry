import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Metric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.PullbackConnection
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
theorem levi_civita_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)
      = pullback_connection_construct g Φ := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem levi_civita_pullback_conjugation_symm
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    pullback_connection_construct g Φ
      = LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ) := rfl

end DifferentialGeometry.PDE.RicciFlow.Pullback
