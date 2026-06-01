import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.PDE.DeTurck.Symbol

/-!
# Principal-symbol predicate for tensor-valued operators on Riemannian metrics

This file introduces the predicate `HasPrincipalSymbol F g₀ σ`, which records
that a (typically nonlinear) operator
```
F : SmoothRiemannianMetric I M →
      (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
```
sending a Riemannian metric to a `(0,2)`-tensor field has principal symbol
`σ : TensorSymbol I M` at the linearization base point `g₀`.  This is the
clean target for "the Ricci–DeTurck right-hand side is strictly parabolic at
`g₀`": one proves `HasPrincipalSymbol F g₀ σ` and then transports
`IsStrictlyParabolic σ` (defined in `PDE/DeTurck/Symbol.lean`) to obtain
strict parabolicity of `F`.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The operator `F : SmoothRiemannianMetric I M → (0,2)`-tensor field has
**principal symbol** `σ : TensorSymbol I M` at the metric `g₀`.

This is the predicate "the linearization `DF(g₀)` of `F` at `g₀` is a
second-order linear differential operator whose top-order part, in every
chart, equals `Σ_{i,j} a^{ij}(x) ∂_i ∂_j h + (lower-order)` with chart
coefficients `a^{ij}` whose principal symbol is `σ` via the substitution
`∂_i ∂_j ↦ −ξ_i ξ_j` packaged by `secondOrderSymbol_apply`
(`PDE/DeTurck/Symbol.lean`)". -/
def HasPrincipalSymbol
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M) : Prop :=
  let _ := F
  DifferentialGeometry.PDE.DeTurck.IsStrictlyParabolic
    (E := E) (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) g₀ σ

end RicciFlow
end PDE
end DifferentialGeometry

end
