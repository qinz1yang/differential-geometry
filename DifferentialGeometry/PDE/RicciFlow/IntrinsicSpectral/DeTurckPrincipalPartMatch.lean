import DifferentialGeometry.PDE.RicciFlow.StrictParabolicAtSelf
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckLinearization

/-!
# Principal-part match between the Ricci–DeTurck RHS and the rough Laplacian

This file records the rigorous *principal-part identification* underlying the
splitting `N(g) := deTurckRicciRHS g_bg g − Δ_∇ g`, where `Δ_∇` is the
connection (rough) Laplacian on `(0,2)`-tensors whose spectrum scales the
spectral Sobolev tower `tensorHs`.

## What is established here

The second-order (principal) part of `deTurckRicciRHS g_bg g`, linearized at any
base metric `g₀` and restricted to **symmetric** `(0,2)`-tensor perturbations —
the space the metric perturbation actually lives in — has principal symbol the
**isotropic symbol** `−|ξ|²_{g₀} · id` (geometer sign, substitution
`∂_a ∂_b ↦ −ξ_a ξ_b`).  This is *exactly* the principal symbol of the
connection/rough Laplacian `Δ_∇ = −∇*∇`, whose eigenvalues `λᵢ ≥ 0`
(`TensorEigenIdx.lambda`) define the weights `(1 + λᵢ)^σ` of `tensorHs`.

Hence the lower-order remainder

  `N(g) := deTurckRicciRHS g_bg g − Δ_∇ g`

is, at the level of the *principal symbol*, genuinely first-order: the two
second-order parts cancel.  The DeTurck gauge cancellation
(`StrictParabolicity.lean`) is precisely what makes the DeTurck principal
operator agree with the isotropic Laplacian symbol rather than with the
gauge-degenerate bare-Ricci symbol.

## Scope (honest)

This file establishes the *symbol-level* principal-part match — the
mathematically decisive Step-0 verification.  It does **not** assemble a global
operator `N : tensorHs (a+2) → tensorHs a` with a `LipschitzWith` constant: that
faces two further, separate obstructions documented in
`DeTurckRHSPointwiseLipschitz.lean` (the jet-versus-value obstruction `O1` and
the model↔Riemannian uniformisation `O2`) and a type-level obstruction (elements
of `tensorHs` are abstract spectral coordinate families, not Riemannian metrics,
so `deTurckRicciRHS`, which consumes two `SmoothRiemannianMetric`, does not even
type-check on `tensorHs` inputs without first building a quasilinear coefficient
realization of the `g`-dependent Christoffel/inverse-Gram coefficients on the
spectral scale).  See the module docstring discussion below.

## Sign convention

Geometer convention `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`, resolvent `(1 − Δ_∇)⁻¹`;
the isotropic principal symbol is `−|ξ|²_{g₀} · id` under `∂_a ∂_b ↦ −ξ_a ξ_b`.
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

/-- **The Ricci–DeTurck RHS principal symbol equals the isotropic
(rough-Laplacian) symbol.**

The strictly-parabolic principal-symbol witness for `deTurckRicciRHS g_bg` at any
base metric `g₀` is the isotropic symbol with coefficient `−|ξ|²_{g₀}` — the
exact principal symbol of the connection (rough) Laplacian `Δ_∇ = −∇*∇` (geometer
sign).  Concretely the witness symbol `σ` equals
`isotropicSymbol _ (deTurckSymbolCoeff g₀)` and satisfies
`HasPrincipalSymbol (deTurckRicciRHS g_bg) g₀ σ`.

This is the symbol-level statement that the second-order parts of
`deTurckRicciRHS g_bg g` and `Δ_∇ g` cancel, so that the remainder
`g ↦ deTurckRicciRHS g_bg g − Δ_∇ g` is first-order at the level of the principal
symbol.  It is `deturck_ricci_rhs_linearization_at_g0` re-exported under a name
that flags its role in the splitting; the witness coefficient
`deTurckSymbolCoeff g₀ x ξ = −|ξ|²_{g₀}` is literally the rough-Laplacian symbol
coefficient. -/
theorem deTurckRicciRHS_principalSymbol_eq_roughLaplacianSymbol
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
      σ = DifferentialGeometry.PDE.DeTurck.isotropicSymbol
            (E := E)
            (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
            (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) ∧
      DifferentialGeometry.PDE.RicciFlow.HasPrincipalSymbol (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        g₀ σ :=
  deturck_ricci_rhs_linearization_at_g0 (I := I) g_bg g₀

/-- **The principal symbol coefficient is the geometer rough-Laplacian symbol.**

At every base point `x` and covector `ξ`, the scalar coefficient of the
Ricci–DeTurck principal symbol is `−|ξ|²_{g₀}` — the same coefficient that the
connection Laplacian `Δ_∇` produces under the substitution `∂_a ∂_b ↦ −ξ_a ξ_b`.
This is the pointwise identity that makes the second-order parts of
`deTurckRicciRHS g_bg g` and `Δ_∇ g` agree (hence cancel in the remainder). -/
theorem deTurckRicciRHS_symbolCoeff_eq_covectorNormSq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (ξ : E) :
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀ x ξ =
      -DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ :=
  DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply (I := I) g₀ x ξ

/-- **The principal symbol acts isotropically on every fibre element.**

Applied to a `(0,2)`-tensor fibre element `t`, the Ricci–DeTurck principal symbol
scales it by `−|ξ|²_{g₀}`: `σ(x, ξ)(t) = (−|ξ|²_{g₀}) • t`.  This is the precise
sense in which the principal part is `Δ_∇` (the isotropic Laplacian) and not a
genuinely tensorial second-order operator: there is no mixing of components at top
order, exactly the DeTurck cancellation. -/
theorem deTurckRicciRHS_principalSymbol_apply_eq_smul
    (g₀ : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = (-DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ)
          • t := by
  rw [DifferentialGeometry.PDE.DeTurck.isotropicSymbol_apply_apply,
    DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff_apply]

/-- **The DeTurck-Ricci and rough-Laplacian principal symbols match on symmetric
perturbations.**

On a **symmetric** input bilinear form `t` (`t v w = t w v`) — the space the metric
perturbation lives in — the isotropic principal-symbol witness `isotropicSymbol _
(deTurckSymbolCoeff g₀)` (coefficient `−|ξ|²_{g₀}`) equals the negation of the bundled
linearized Ricci–DeTurck symbol `deTurckSymbol g₀ g_bg`, which on symmetric `t` is the
gauge-cancelled isotropic scaling `|ξ|²_{g₀} • t`.  Equivalently, the two candidate
second-order parts — the DeTurck RHS principal part and the rough Laplacian
`Δ_∇ = −∇*∇` — coincide at the symbol level on symmetric perturbations, so the
remainder `N(g) = deTurckRicciRHS g_bg g − Δ_∇ g` carries no second-order content
there.

The proof is `deTurckRicciRHS_principal_symbol_equals_deTurckSymbol`, whose symmetry
hypothesis `ht` is what produces the gauge cancellation. -/
theorem deturck_ricci_principal_symbol_matches_rough_laplacian_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (x : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    DifferentialGeometry.PDE.DeTurck.isotropicSymbol
        (E := E)
        (fun x : M => TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
        (DifferentialGeometry.PDE.DeTurck.deTurckSymbolCoeff (I := I) g₀) x ξ t
      = - DifferentialGeometry.PDE.DeTurck.deTurckSymbol (I := I) g₀ g_bg x ξ t :=
  DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS_principal_symbol_equals_deTurckSymbol
    (I := I) g₀ g_bg x ξ t ht

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
