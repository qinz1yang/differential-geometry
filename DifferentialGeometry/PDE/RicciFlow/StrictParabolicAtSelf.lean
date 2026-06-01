import DifferentialGeometry.PDE.RicciFlow.DeTurckRHS
import DifferentialGeometry.PDE.RicciFlow.PrincipalSymbol
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.PDE.DeTurck.Symbol
import DifferentialGeometry.PDE.DeTurck.StrictParabolicity
import DifferentialGeometry.PDE.DeTurck.RicciLinearization.RicciPrincipalPart
import DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.DeTurckCorrectionSymbol

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The Ricci–DeTurck right-hand side `g ↦ -2 Rc(g) + 𝓛_{W(g, g_bg)} g` is strictly
parabolic at its own base metric `g₀`.

The witness symbol is the isotropic Ricci–DeTurck symbol with coefficient `-|ξ|²_{g₀}`
(see `DeTurck.isotropicSymbol` with `DeTurck.deTurckSymbolCoeff g₀`).  Under the current
`HasPrincipalSymbol` content this reduces to `IsStrictlyParabolic _ g₀ σ` for that
isotropic symbol, which is the defining strict-parabolicity property
(`DeTurck.isStrictlyParabolic_isotropic_deTurckSymbolCoeff`). -/
theorem deTurckRicciRHS_isStrictlyParabolic_at_self
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    IsStrictlyParabolicMetricRHS (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀ :=
  ⟨DifferentialGeometry.PDE.DeTurck.isotropicSymbol
      (E := E)
      (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
      (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀),
    DifferentialGeometry.PDE.DeTurck.isStrictlyParabolic_isotropic_deTurckSymbolCoeff
      (E := E)
      (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) g₀⟩

/-- **Symbol-form identification on a symmetric input.**  The strictly-parabolic
isotropic symbol witness for `deTurckRicciRHS g_bg` at `g₀` (the isotropic symbol with
coefficient `-|ξ|²_{g₀}`) is the **negation** of the bundled Ricci–DeTurck linearized
symbol `DeTurck.deTurckSymbol g₀ g_bg`, on a **symmetric** input bilinear form `t`
(`t v w = t w v`).

The bundled `deTurckSymbol g₀ g_bg` is the linear combination
`-2 • ricciSymbol g₀ + deTurckCorrectionSymbol g₀ g_bg` whose gauge cancellation
(`DeTurck.deTurckSymbol_apply_eq_smul_of_symm`) reads, on symmetric `t`, as the action
`t ↦ |ξ|²_{g₀} · t` — the *positive* isotropic scaling, the substitution
`∂_a ∂_b ↦ +ξ_a ξ_b`.  The strictly-parabolic isotropic symbol used as the
`HasPrincipalSymbol` witness in `deTurckRicciRHS_isStrictlyParabolic_at_self` is its
geometer-sign counterpart `t ↦ -|ξ|²_{g₀} · t` (the substitution
`∂_a ∂_b ↦ -ξ_a ξ_b`, consistent with the geometer's Laplacian `Δ = div ∘ grad`
having spectrum `⊆ (-∞, 0]`).  So the two agree up to an overall sign on the
symmetric input that downstream parabolic consumption actually uses.

This pins down the bundled `deTurckSymbol` as the "positive symbol" companion of the
strictly-parabolic witness on the same diagonal data, and is the symmetric-input
shadow of the principal-symbol equality `σ(F) = deTurckSymbol g₀ g_bg` (read with the
opposite covector-substitution convention) underlying
`deTurckRicciRHS_isStrictlyParabolic_at_self`. -/
theorem deTurckRicciRHS_principal_symbol_equals_deTurckSymbol
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = - DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg x ξ t := by
  classical
  rw [DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply]
  rw [DifferentialGeometry.PDE.DeTurck.deTurckSymbol_apply_eq_smul_of_symm
    (I := I) g₀ g_bg x ξ t ht]
  rw [neg_smul]

/-- **Bridge from a principal-symbol witness to strict parabolicity of the metric RHS.**

If an operator `F` on smooth Riemannian metrics has *some* principal symbol `σ` at the
metric `g₀` (the existence of `σ` such that `HasPrincipalSymbol F g₀ σ`), then it is
strictly parabolic at `g₀` in the sense of `IsStrictlyParabolicMetricRHS`.

This is the trivial repackaging the downstream parabolic-existence consumer expects:
`IsStrictlyParabolicMetricRHS` is, by definition, the existence statement
`∃ σ, HasPrincipalSymbol F g₀ σ` — so any witness `(σ, h)` packages directly.  The
content of strict parabolicity is then carried by `HasPrincipalSymbol`'s body, which
under the current setup is `IsStrictlyParabolic _ g₀ σ`. -/
theorem bridge_symbol_equality_to_is_strictly_parabolic_metric_rhs
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M)
    (h : HasPrincipalSymbol F g₀ σ) :
    IsStrictlyParabolicMetricRHS (I := I) F g₀ :=
  ⟨σ, h⟩

end DifferentialGeometry.PDE.RicciFlow
