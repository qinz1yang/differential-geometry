import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionSymbol
import DifferentialGeometry.Analysis.Parabolic.StrictParabolicity
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic

/-!
# Principal symbol of the linearized Ricci–DeTurck right-hand side

The linearization of `deTurckRicciRHS g_bg` at a base metric `g₀`, viewed as a
second-order operator on `(0,2)`-tensor perturbations, has principal symbol the
geometer-sign isotropic Ricci–DeTurck symbol `isotropicSymbol _ (deTurckSymbolCoeff g₀)`
(scalar coefficient `c(x, ξ) = -|ξ|²_{g₀}`). This is the same witness shape used by
the strict-parabolicity statement of the operator at the same metric, recorded here
for the spectral principal-part match.
-/

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Principal-symbol identification for the linearization of the
Ricci–DeTurck right-hand side at `g₀`.**

The linearization of `deTurckRicciRHS g_bg` at the base metric `g₀`, viewed as a
second-order linear differential operator on `(0,2)`-tensor perturbations, has a
principal symbol given by the **geometer-sign isotropic Ricci–DeTurck symbol**
`isotropicSymbol _ (deTurckSymbolCoeff g₀)` — the symbol whose scalar coefficient
is `c(x, ξ) = -|ξ|²_{g₀}` (substitution `∂_a ∂_b ↦ -ξ_a ξ_b`, consistent with
the geometer's convention `Δ = div ∘ grad` having spectrum `⊆ (-∞, 0]`).

This is the same witness shape used in
`DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_isStrictlyParabolic_at_self`
(the strict-parabolicity statement of the same operator at the same metric); on a
**symmetric** input bilinear form `t` this isotropic witness equals the negation of
the bundled linearized symbol `DeTurck.deTurckSymbol g₀ g_bg`, as recorded in
`DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_principal_symbol_equals_deTurckSymbol`
(the sign mismatch reflects the opposite covector-substitution conventions used to
build the two symbols, not a genuine ambiguity in the principal part).  We pick the
geometer-sign witness here because it is the one already used by the downstream
strict-parabolicity consumer. -/
theorem deturck_ricci_rhs_linearization_at_g0 [I.Boundaryless]
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
      σ = DifferentialGeometry.PDE.DeTurck.isotropicSymbol
            (E := E)
            (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
            (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) ∧
      DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        g₀ σ :=
  ⟨DifferentialGeometry.PDE.DeTurck.isotropicSymbol
      (E := E)
      (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
      (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀),
    rfl,
    DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_hasPrincipalSymbol_at_self g₀ g_bg⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
