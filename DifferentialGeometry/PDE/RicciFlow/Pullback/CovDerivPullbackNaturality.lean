import DifferentialGeometry.PDE.RicciFlow.Pullback.LeviCivitaConjugation
import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF

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

/-- Naturality of the Levi-Civita covariant derivative under pullback by a
diffeomorphism. By Koszul uniqueness, the Levi-Civita connection of the
pullback metric `Φ*g` is the pullback-by-conjugation of the Levi-Civita
connection of `g`. The project records that pullback connection by the
construction `pullback_connection_construct g Φ`, which is by definition
`LeviCivita (Φ*g)`. Hence, at the level of bundled covariant derivatives,
the two connections coincide by `rfl`.

For any smooth vector fields `X, Y` on `M`, this identity unfolds — upon
specialising both sides at a point — to the pointwise naturality formula
`∇^g_{Φ_*X} (Φ_*Y) = Φ_* (∇^{Φ*g}_X Y)`, which is the chain-rule-style
statement of "the pullback connection is the conjugate of `∇^g`". -/
theorem covariant_derivative_of_pullback_vf_naturality
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)
      = pullback_connection_construct g Φ := rfl

end DifferentialGeometry.PDE.RicciFlow.Pullback
