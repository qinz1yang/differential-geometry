import DifferentialGeometry.PDE.RicciFlow.Pullback.LeviCivitaConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.MLieBracketNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.PullbackConnection
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.CurvatureBundling

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

/-- **Pullback-by-conjugation for the Riemann curvature operator (connection form).**
The Levi-Civita covariant derivative of the pullback metric `Φ*g` agrees with the
explicit pullback-by-conjugation construction `pullback_connection_construct g Φ`.

This is the connection-level identity that drives the section-level naturality of the
Riemann tensor under the diffeomorphism `Φ`: since `riemannSec` is defined as a
polynomial expression in the covariant derivative `cov.toFun`, equality of the
underlying connections yields equality of every derived curvature quantity.

The identity is reflexive because `pullback_connection_construct g Φ` is, by
definition (see `PullbackConnection.lean`), `LeviCivita (Diffeomorph.pullbackMetric g Φ)`,
which is precisely the LHS. -/
theorem riemann_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)
      = pullback_connection_construct g Φ := rfl

end DifferentialGeometry.PDE.RicciFlow.Pullback
