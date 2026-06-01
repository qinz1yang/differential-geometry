import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.Integral.Connection.LeviCivita

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The pullback connection induced by a diffeomorphism `Φ : M ≃ₘ⟮I, I⟯ M`
acting on a Riemannian metric `g`. By the Koszul identity, the unique
torsion-free metric-compatible connection on `(M, Φ*g)` is the Levi-Civita
connection of the pullback metric `Diffeomorph.pullbackMetric g Φ`. The
pullback-by-conjugation formula `(Φ⁻¹)_* ∘ ∇^g ∘ Φ_*` produces this same
connection by Koszul-uniqueness; here we take the equivalent, directly
constructible side `LeviCivita (Φ*g)`. -/
noncomputable def pullback_connection_construct
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    CovariantDerivative I E (TangentSpace I : M → Type _) :=
  LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)

/-- The pullback connection `pullback_connection_construct g Φ` is
torsion-free. This is immediate from the fact that the Levi-Civita
connection of any smooth Riemannian metric is torsion-free. -/
theorem pullback_connection_torsion_free
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    (pullback_connection_construct g Φ).torsion = 0 :=
  LeviCivita_torsion_eq_zero (I := I) (Diffeomorph.pullbackMetric g Φ)

/-- The pullback connection `pullback_connection_construct g Φ` is
metric-compatible with the pullback metric `Diffeomorph.pullbackMetric g Φ`.
This is immediate from the metric-compatibility of the Levi-Civita
connection of any smooth Riemannian metric. -/
theorem pullback_connection_metric_compatible
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    IsMetricCompatible (pullback_connection_construct g Φ)
      (Diffeomorph.pullbackMetric g Φ) :=
  LeviCivita_isMetricCompatible (I := I) (Diffeomorph.pullbackMetric g Φ)

end DifferentialGeometry.PDE.RicciFlow.Pullback
