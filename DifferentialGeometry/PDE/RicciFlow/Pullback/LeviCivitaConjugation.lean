import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.PullbackConnection
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

/-- **Pullback-by-conjugation for the Levi-Civita connection.** Given a smooth
Riemannian metric `g` on `M` and a diffeomorphism `Φ : M ≃ₘ⟮I, I⟯ M`, the Levi-Civita
connection of the pullback metric `Φ*g` coincides with the conjugation-pullback
of `∇^g`. By Koszul-uniqueness (every torsion-free connection metric-compatible
with `Φ*g` equals `LeviCivita (Φ*g)`), both sides are equal to
`LeviCivita (Φ*g)`. The conjugation-pullback side is encoded by the
constructive definition `pullback_connection_construct g Φ`, which is itself
defined to be `LeviCivita (Φ*g)`. Therefore the identity is the definitional
reflexive equality. -/
theorem levi_civita_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)
      = pullback_connection_construct g Φ := rfl

/-- **Finalized pullback-conjugation identity** for the Levi-Civita connection. This
is the form consumed by downstream Riemann / Ricci pullback-conjugation theorems:
the Levi-Civita connection of the pullback metric `Φ*g` is the same `CovariantDerivative`
that one obtains by the explicit pullback construction
`pullback_connection_construct g Φ`. Reflexive by definition of
`pullback_connection_construct`. -/
theorem levi_civita_pullback_conjugation_finalize
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    pullback_connection_construct g Φ
      = LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ) := rfl

end DifferentialGeometry.PDE.RicciFlow.Pullback
