import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Analysis.Parabolic.PrincipalSymbol
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionPrincipalSymbolRemainder
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula

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
`IsStrictlyParabolic σ` (defined in `Analysis/Parabolic/PrincipalSymbol.lean`) to obtain
strict parabolicity of `F`.

## The predicate genuinely constrains `F`'s linearization, not just its value

`σ` is required to be the principal symbol of the *linearization* `D F(g₀)`, not a
free isotropic reference symbol.  The bare carrier type
`SmoothRiemannianMetric I M → (∀ x, T_xM →L T_xM →L ℝ)` records only the *values* of
`F`, so the differential structure must be supplied by witnessing the chart
second-order part of `F`'s directional derivative explicitly:

* `IsChartLinearizationSecondOrderPart F g₀ P` — the family
  `P : ChartMetricPerturbation E → (α : M) → (i j) → E → ℝ` is the genuine **chart
  `∂²h`-coefficient of `D F(g₀)`**.  Concretely, in every chart `α` and for every chart
  metric perturbation `h`, the chart-coordinate component
  `y ↦ F g x (e_i^α x) (e_j^α x)` of the operator, perturbed along the family
  `s ↦ g₀ ⊕ s·h`, has chart second-order `∂²h`-content `P h α i j` — the part of the
  directional derivative `D_h F(g₀)` carrying two chart derivatives of `h`.  This is
  the abstract analogue of the concrete chart second-order parts
  `chartRicciSecondOrderPart` and `chartDeTurckCorrSecondOrderPart`.

* `HasPrincipalSymbol F g₀ σ` then records that some chart second-order part `P` of
  `D F(g₀)` exists (`IsChartLinearizationSecondOrderPart F g₀ P`) whose principal
  symbol — read off by the substitution `∂_a∂_b h_{cd} ↦ −ξ_a ξ_b · t_{cd}` (geometer
  sign) modulo a genuinely first-order remainder — is `σ`, and that `σ` is the
  strictly-parabolic isotropic symbol `−|ξ|²_{g₀} · id` on the symmetric perturbation
  space.

Neither clause is satisfiable for an arbitrary `F`.  In particular the **zero operator**
`F := fun _ _ => 0` has constant chart components, so its only chart second-order part is
`P = 0`; its principal symbol is therefore the zero symbol, which is *not* the
strictly-parabolic `−|ξ|²_{g₀} · id` (the latter is nonzero for `ξ ≠ 0`, since
`|ξ|²_{g₀} > 0`).  Hence `∃ σ, HasPrincipalSymbol (fun _ _ => 0) g₀ σ` fails: the symbol
no longer ignores `F`.  The same obstruction rejects any first-order, zeroth-order, or
anisotropic operator, whose chart `∂²h`-coefficient's symbol is not the isotropic
`−|ξ|²_{g₀} · id`.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The chart-`α`-pushforward frame vector at `x`: the tangent vector whose chart-`α`
trivialisation is the constant model-basis vector `chartModelBasis E i`.  As `x` varies
over the chart-`α` source these form a smooth local frame for `TangentSpace I`. -/
def chartPushforwardFrameVec (α : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symmL ℝ x (chartModelBasis E i)

/-- The chart-`α` `(i, j)`-**component of `F g`**, pulled back to the chart target
`E ⊇ (extChartAt I α).target` via the chart inverse:
`y ↦ F g ((extChartAt I α).symm y) (e_i^α) (e_j^α)`, where
`e_i^α = chartPushforwardFrameVec α i` is the chart-`α`-pushforward frame vector.

This scalar function on `E` is the chart-coordinate datum whose chart second-order
`∂²h`-content (under a metric perturbation) the principal symbol of `D F(g₀)` reads off.
For the concrete Ricci–DeTurck operator it is the chart component whose linearization is
`(-2)·chartRicciSecondOrderPart + chartDeTurckCorrSecondOrderPart + (lower order)`. -/
def chartFComponentOnE
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    F g ((extChartAt I α).symm y)
      (chartPushforwardFrameVec (I := I) α i ((extChartAt I α).symm y))
      (chartPushforwardFrameVec (I := I) α j ((extChartAt I α).symm y))

/-- `IsMetricPerturbationFamily g₀ α h gfam` says the smooth one-parameter family
`gfam : ℝ → SmoothRiemannianMetric I M` realises the perturbation line
`s ↦ g₀ ⊕ s·h` through the chart perturbation `h`, **to second order in the chart
`y`-jet, with `s`-`y` smoothness**, at `s = 0`, in chart-`α`-coordinate components.

The clauses are:

* `gfam 0 = g₀` — the family passes through `g₀` at `s = 0`;
* `(d/ds) g_{ij}(gfam s)(y)|_{s = 0} = h_{ij}(y)` — the chart-Gram **value** moves along
  `h` with unit speed (the original pin; the downstream zero-operator guard depends on it);
* **(joint smoothness)** for each `i, j`, the map
  `(s, y) ↦ g_{ij}(gfam s)(y)` is `C^∞` at every point of `Set.univ ×ˢ interior target`,
  so that one may differentiate the chart-Gram in `s` and in `y` freely and commute
  `(d/ds)` with the chart partials `∂_y` (Clairaut/Schwarz);
* **(first `y`-jet pin)** `(d/ds) ∂_p g_{ij}(gfam s)(y)|_{s = 0} = ∂_p h_{ij}(y)`, the
  first chart partial of the Gram moves along the first chart partial of `h`;
* **(second `y`-jet pin)** `(d/ds) ∂_p∂_q g_{ij}(gfam s)(y)|_{s = 0} = ∂_p∂_q h_{ij}(y)`,
  the iterated second chart partial of the Gram moves along that of `h`.

The two `y`-jet pins are exactly the inputs the chart second-order symbol calculus needs:
the linearized Ricci principal symbol carries `∂²h`, so the `s`-derivative of the chart
DeTurck–Ricci tower at a chart-interior point reads off `∂²h` through the second `y`-jet
pin, while the first-order remainder reads off `∂h` through the first `y`-jet pin.

The first-order (derivative) form — rather than an exact affine identity for all `s` — is
what makes the family **realisable by genuine positive-definite metrics**: a small
symmetric perturbation `g₀ + s·χ·h` with a chart cutoff `χ ≡ 1` near `y` stays
positive-definite for `s` small and has the prescribed `s`-derivatives of every chart
`y`-jet at `s = 0` (since `χ ≡ 1` makes the family affine-in-`s` near `y`, with all `∂χ`
factors vanishing), while an exact global `g₀ + s·h` would fail positivity for an
unbounded `h`.  Every clause is satisfied by such an affine cutoff family, so the
predicate is non-vacuous. -/
def IsMetricPerturbationFamily
    (g₀ : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (gfam : ℝ → SmoothRiemannianMetric I M) : Prop :=
  gfam 0 = g₀ ∧
    (∀ (i j : Fin (Module.finrank ℝ E)) {y : E}, y ∈ interior (extChartAt I α).target →
      HasDerivAt (fun s : ℝ => chartGramOnE (I := I) (gfam s) α i j y) (h i j y) 0) ∧
    (∀ (i j : Fin (Module.finrank ℝ E)) {y : E},
        y ∈ interior (extChartAt I α).target →
        ContDiffAt ℝ ∞
          (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) α i j p.2) (0, y)) ∧
    (∀ (i j p : Fin (Module.finrank ℝ E)) {y : E},
        y ∈ interior (extChartAt I α).target →
        HasDerivAt
          (fun s : ℝ => partialDeriv (E := E) p (chartGramOnE (I := I) (gfam s) α i j) y)
          (partialDeriv (E := E) p (h i j) y) 0) ∧
    (∀ (i j p q : Fin (Module.finrank ℝ E)) {y : E},
        y ∈ interior (extChartAt I α).target →
        HasDerivAt
          (fun s : ℝ =>
            partialDeriv (E := E) p
              (partialDeriv (E := E) q (chartGramOnE (I := I) (gfam s) α i j)) y)
          (partialDeriv (E := E) p (partialDeriv (E := E) q (h i j)) y) 0)

/-- `IsFirstOrderInPerturbation R` says the family
`R : ChartMetricPerturbation E → (α : M) → (i j) → E → ℝ` carries **at most one** chart
derivative of a component field of `h`, and **vanishes when that one derivative is
absent**: at any chart-interior point `y`, if `h`'s component values and first chart
partial derivatives all vanish at `y`, then `R h α i j y = 0`.

This is the abstract analogue of `chartRicciFirstOrderRemainder_eq_first_order_sum` /
`chartDeTurckCorrFirstOrderRemainder_eq_first_order_sum`: those exhibit the concrete
remainders as finite sums of terms `(coeff) · partialDeriv _ (h _ _) _`, each carrying a
single chart derivative `partialDeriv p (h a b) y` of a component field of `h`; such a sum
vanishes once every `partialDeriv p (h a b) y` (and `h a b y`) is `0`.  A first-order
remainder is invisible to the second-order principal symbol: the `∂²h ↦ ξξ` substitution
is realised by a perturbation whose value and first chart derivatives vanish at `y` (only
the *second* chart derivatives are nonzero), on which `R` therefore vanishes. -/
def IsFirstOrderInPerturbation
    (R : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
         Fin (Module.finrank ℝ E) → E → ℝ) : Prop :=
  ∀ (α : M) (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E))
      {y : E}, y ∈ interior (extChartAt I α).target →
      (∀ a b, h a b y = 0) →
      (∀ p a b, partialDeriv (E := E) p (h a b) y = 0) →
      R h α i j y = 0

/-- `P : ChartMetricPerturbation E → (α : M) → (i j) → E → ℝ` **is the chart
`∂²h`-coefficient of the linearization `D F(g₀)`** when, in every chart `α`, for every
chart perturbation `h` and every realising family `gfam` of `s ↦ g₀ ⊕ s·h`
(`IsMetricPerturbationFamily g₀ α h gfam`), the directional derivative of the chart
`(i, j)`-component
`(d/ds) (chartFComponentOnE F (gfam s) α i j y)|_{s = 0} = D_h F(g₀)`
splits, at chart-interior points, as
`P h α i j y` (the part carrying **two** chart derivatives of `h`) plus a genuinely
**first-order** remainder `R h α i j y` (`IsFirstOrderInPerturbation R`, carrying at most
one chart derivative of `h`).

This is the abstract analogue of
`chartRicciSecondOrderPart_eq_principalSymbol_add_remainder` and
`chartDeTurckCorrSecondOrderPart_eq_principalSymbol_add_remainder`, which identify the
concrete chart second-order parts of the Ricci and DeTurck-correction operators.  The
condition references `F`'s actual values through `chartFComponentOnE F (gfam s)` and its
`s`-derivative, so it is genuinely about `F`: a different operator has a different chart
component, hence a different directional derivative, hence a different second-order part.
The **zero operator** has constant chart component `0`, so its directional derivative is
`0`; the only admissible `(P, R)` then has `P = 0` (the `∂²h`-coefficient of `0`),
which has principal symbol `0`. -/
def IsChartLinearizationSecondOrderPart
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (P : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
         Fin (Module.finrank ℝ E) → E → ℝ) : Prop :=
  ∃ R : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → E → ℝ,
    IsFirstOrderInPerturbation (I := I) R ∧
      ∀ (α : M) (h : ChartMetricPerturbation E)
          (gfam : ℝ → SmoothRiemannianMetric I M),
          IsMetricPerturbationFamily (I := I) g₀ α h gfam →
          ∀ (i j : Fin (Module.finrank ℝ E)) {y : E},
            y ∈ interior (extChartAt I α).target →
            deriv (fun s : ℝ => chartFComponentOnE (I := I) F (gfam s) α i j y) 0 =
              P h α i j y + R h α i j y

/-- The **symbol test perturbation** `symbolTestPerturbation x α ξ t` for a base point
`x`, a chart `α`, a covector `ξ`, and a fibre bilinear form `t`: the chart perturbation
$$h^{\xi, t}_{cd}(y) = \tfrac12\,\bigl(\langle\xi, y - y_0\rangle\bigr)^2\, t_{cd},
  \qquad y_0 = \operatorname{extChartAt} I\,\alpha\, x,$$
where `⟨ξ, ·⟩` is the chart linear functional `z ↦ ∑_a ξ_a z_a` with
`ξ_a = (chartModelBasis E).repr ξ a` and `t_{cd} = formComp x t c d`.

By construction its component value and first chart derivatives vanish at `y_0` and its
second chart derivatives realise the substitution datum
`∂_a ∂_b h^{ξ,t}_{cd}(y_0) = ξ_a ξ_b · t_{cd}`.  It is the chart perturbation that
implements the principal-symbol substitution `∂_a∂_b h_{cd} ↦ ξ_a ξ_b · t_{cd}` on the
chart second-order part: evaluating a chart `∂²h`-coefficient on it at `y_0` reads off the
principal symbol.  It is symmetric in `(c, d)` exactly when `t` is symmetric
(`formComp_symm`). -/
def symbolTestPerturbation (x : M) (α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) : ChartMetricPerturbation E where
  toFun c d := fun y =>
    (1 / 2 : ℝ) *
      ((∑ a : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ a *
            (chartModelBasis E).repr (y - extChartAt I α x) a)) ^ 2 *
      formComp (I := I) x t c d
  symm' c d y := by rw [formComp_symm (I := I) x t ht c d]
  smooth' c d := by
    have hsum : ContDiff ℝ ∞ (fun y : E =>
        ∑ a : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr ξ a *
            (chartModelBasis E).repr (y - extChartAt I α x) a) := by
      refine ContDiff.sum (fun a _ => ?_)
      refine contDiff_const.mul ?_
      have hlin : (fun y : E => (chartModelBasis E).repr (y - extChartAt I α x) a) =
          fun y : E => (chartModelBasis E).coord a (y - extChartAt I α x) := by
        funext y; rw [Module.Basis.coord_apply]
      rw [hlin]
      exact (((chartModelBasis E).coord a).toContinuousLinearMap.contDiff).comp
        (contDiff_id.sub contDiff_const)
    exact ContDiff.mul (ContDiff.mul contDiff_const (hsum.pow 2)) contDiff_const

/-- The chart linear functional underlying the symbol test perturbation:
`testLinear x α ξ y = ∑_a ξ_a (y - y₀)_a`, with `y₀ = extChartAt I α x`.  It is the affine
functional whose square (scaled by `½ t_{cd}`) is the test perturbation. -/
private def testLinear (x α : M) (ξ : E) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr ξ a * (chartModelBasis E).repr (y - extChartAt I α x) a

private lemma symbolTestPerturbation_apply (x α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (c d : Fin (Module.finrank ℝ E)) (y : E) :
    symbolTestPerturbation (I := I) x α ξ t ht c d y =
      (1 / 2 : ℝ) * (testLinear (I := I) x α ξ y) ^ 2 * formComp (I := I) x t c d := rfl

/-- The chart linear functional `testLinear` vanishes at the base chart point
`y₀ = extChartAt I α x`. -/
private lemma testLinear_self (x α : M) (ξ : E) :
    testLinear (I := I) x α ξ (extChartAt I α x) = 0 := by
  simp [testLinear]

/-- The symbol test perturbation has vanishing component value at the base chart point
`y₀ = extChartAt I α x`. -/
lemma symbolTestPerturbation_apply_self (x α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (c d : Fin (Module.finrank ℝ E)) :
    symbolTestPerturbation (I := I) x α ξ t ht c d (extChartAt I α x) = 0 := by
  rw [symbolTestPerturbation_apply, testLinear_self]; ring

/-- The chart linear functional `testLinear x α ξ` is differentiable everywhere (it is an
affine functional in `y`). -/
private lemma testLinear_differentiableAt (x α : M) (ξ : E) (y : E) :
    DifferentiableAt ℝ (testLinear (I := I) x α ξ) y := by
  refine DifferentiableAt.fun_sum (fun a _ => ?_)
  refine (differentiableAt_const _).mul ?_
  have hlin : (fun y : E => (chartModelBasis E).repr (y - extChartAt I α x) a) =
      fun y : E => (chartModelBasis E).coord a (y - extChartAt I α x) := by
    funext z; rw [Module.Basis.coord_apply]
  rw [hlin]
  exact (((chartModelBasis E).coord a).toContinuousLinearMap.differentiableAt).comp y
    ((differentiableAt_id).sub (differentiableAt_const _))

/-- The symbol test perturbation has vanishing first chart partial derivatives at the base
chart point `y₀ = extChartAt I α x`: every `∂_p h^{ξ,t}_{cd}(y₀) = 0`, because the affine
factor `testLinear` vanishes there.  Together with `symbolTestPerturbation_apply_self`, the
`0`-jet and `1`-jet of the test perturbation vanish at `y₀`. -/
lemma partialDeriv_symbolTestPerturbation_self (x α : M) (ξ : E)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (ht : ∀ v w, t v w = t w v)
    (p c d : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p
        (symbolTestPerturbation (I := I) x α ξ t ht c d) (extChartAt I α x) = 0 := by
  have hfun : (symbolTestPerturbation (I := I) x α ξ t ht c d) =
      fun y => ((1 / 2 : ℝ) * formComp (I := I) x t c d) *
        (testLinear (I := I) x α ξ y) ^ 2 := by
    funext y; rw [symbolTestPerturbation_apply]; ring
  rw [hfun]
  rw [partialDeriv_const_mul (E := E) ((1 / 2 : ℝ) * formComp (I := I) x t c d)
      (fun y => (testLinear (I := I) x α ξ y) ^ 2)
      (((testLinear_differentiableAt (I := I) x α ξ
        (extChartAt I α x)).pow 2))]
  have hpow : (fun y => (testLinear (I := I) x α ξ y) ^ 2) =
      fun y => (testLinear (I := I) x α ξ y) * (testLinear (I := I) x α ξ y) := by
    funext y; ring
  rw [hpow,
    partialDeriv_mul (E := E) (testLinear (I := I) x α ξ) (testLinear (I := I) x α ξ)
      (testLinear_differentiableAt (I := I) x α ξ (extChartAt I α x))
      (testLinear_differentiableAt (I := I) x α ξ (extChartAt I α x)),
    testLinear_self]
  ring

/-- `σ` **is the principal symbol of the chart second-order part `P`** at `g₀` when, on the
symmetric perturbation space, `σ` is recovered from `P` by the geometer's principal-symbol
substitution `∂_a∂_b h_{cd} ↦ −ξ_a ξ_b · t_{cd}`, and `σ` is the strictly-parabolic
isotropic symbol `−|ξ|²_{g₀} · id`.

Concretely, for every base point `x`, every nonzero covector `ξ`, and every symmetric
fibre form `t`:

* **(symbol reads off `P`)** evaluating `P` on the symbol test perturbation
  `symbolTestPerturbation x x ξ t` — the chart perturbation whose `∂²h`-datum is
  `+ξ_a ξ_b · t_{cd}` — at the chart image of `x` reproduces the **negated** symbol
  `σ x ξ`'s `(i, j)`-component `−(σ x ξ t)(e_i, e_j)` (the geometer's `∂_a∂_b ↦ −ξ_aξ_b`
  reads with a sign against the `+ξ_aξ_b` test datum); and
* **(strict parabolicity)** `σ x ξ t = −|ξ|²_{g₀} · t` with `0 < |ξ|²_{g₀}`.

The first clause genuinely ties `σ` to `P` (a different `P` reads off a different `σ`); the
second forces `σ` nonzero (`|ξ|²_{g₀} > 0`).  Together they rule out the zero operator: its
chart second-order part is `P = 0`, so the first clause forces `σ x ξ t = 0`, contradicting
the second (`−|ξ|²_{g₀} · t ≠ 0` for `t ≠ 0`). -/
def IsPrincipalSymbolOfSecondOrderPart
    (g₀ : SmoothRiemannianMetric I M)
    (P : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
         Fin (Module.finrank ℝ E) → E → ℝ)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M) : Prop :=
  ∀ (x : M) (ξ : E), ξ ≠ 0 →
    ∀ t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ,
      (∀ v w, t v w = t w v) →
        (∀ ht : ∀ v w, t v w = t w v, ∀ i j : Fin (Module.finrank ℝ E),
            P (symbolTestPerturbation (I := I) x x ξ t ht) x i j (extChartAt I x x) =
              - (σ x ξ t) ((chartModelBasis E) i) ((chartModelBasis E) j)) ∧
          σ x ξ t =
              (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ) •
                t ∧
            0 < DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ

/-- The operator `F : SmoothRiemannianMetric I M → (0,2)`-tensor field has
**principal symbol** `σ : TensorSymbol I M` at the metric `g₀`.

This is the predicate "`σ` is the principal symbol of the linearization `D F(g₀)`": there
is a chart second-order part `P` of `D F(g₀)`
(`IsChartLinearizationSecondOrderPart F g₀ P` — `P` is the genuine chart `∂²h`-coefficient
of `F`'s directional derivative at `g₀`, the abstract analogue of
`chartRicciSecondOrderPart`/`chartDeTurckCorrSecondOrderPart`), and `σ` is the principal
symbol of that *same* second-order part (`IsPrincipalSymbolOfSecondOrderPart g₀ P σ`): the
`∂_a∂_b h ↦ −ξ_aξ_b t` substitution of `P` is `σ`, and on the symmetric perturbation space
`σ` acts as the geometer-sign isotropic symbol
`−|ξ|²_{g₀} · t` with strictly positive coefficient `|ξ|²_{g₀} > 0` — the DeTurck
gauge-cancelled Laplacian symbol.

This is **not** satisfiable for an arbitrary `F`: the symbol no longer ignores `F`.  An
operator whose chart `∂²h`-coefficient is not the isotropic `|ξ|²_{g₀} · id` on symmetric
tensors — in particular the **zero operator**, whose only chart second-order part is `0`
(symbol `0 ≠ −|ξ|²_{g₀} · id`), and any first-order, zeroth-order or anisotropic operator
— admits no admissible `(P, σ)`, hence `∃ σ, HasPrincipalSymbol F g₀ σ` fails. -/
def HasPrincipalSymbol
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (g₀ : SmoothRiemannianMetric I M)
    (σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M) : Prop :=
  ∃ P : ChartMetricPerturbation E → M → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → E → ℝ,
    IsChartLinearizationSecondOrderPart (I := I) F g₀ P ∧
      IsPrincipalSymbolOfSecondOrderPart (I := I) g₀ P σ

/-- From a principal-symbol witness, recover that `σ` acts as the geometer-sign isotropic
symbol `−|ξ|²_{g₀} · t` on symmetric inputs, with strictly negative coefficient
(`0 < |ξ|²_{g₀}`).  This is the strict-parabolicity content of the principal symbol on the
symmetric perturbation space. -/
theorem HasPrincipalSymbol.isotropic_of
    {F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)}
    {g₀ : SmoothRiemannianMetric I M}
    {σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M}
    (h : HasPrincipalSymbol (I := I) F g₀ σ)
    (x : M) (ξ : E) (hξ : ξ ≠ 0)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    σ x ξ t =
        (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ) • t ∧
      0 < DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ := by
  obtain ⟨_, _, hσ⟩ := h
  exact (hσ x ξ hξ t ht).2

/-- A principal symbol is **nonzero** at a nonzero covector: applied to a nonzero
symmetric input it scales by the strictly-negative coefficient `−|ξ|²_{g₀} ≠ 0`.

This is the formal obstruction that rules out the zero operator (and any
first/zeroth-order or anisotropic operator): the principal symbol of `D F(g₀)` cannot be
the zero symbol, because it acts as `−|ξ|²_{g₀} · id` with `|ξ|²_{g₀} > 0`. -/
theorem HasPrincipalSymbol.symbol_apply_eq_neg_normSq_smul
    {F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)}
    {g₀ : SmoothRiemannianMetric I M}
    {σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M}
    (h : HasPrincipalSymbol (I := I) F g₀ σ)
    (x : M) (ξ : E) (hξ : ξ ≠ 0)
    (t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (ht : ∀ v w, t v w = t w v) :
    σ x ξ t =
      (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ) • t :=
  (h.isotropic_of x ξ hξ t ht).1

/-- The chart `(i, j)`-component of the **zero operator** is the constant function `0` on
the chart target, for every metric.  This is the source of the zero operator's failure to
be parabolic: its directional derivative — hence its chart second-order part — is `0`. -/
@[simp] lemma chartFComponentOnE_zero_operator
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartFComponentOnE (I := I)
      (fun (_ : SmoothRiemannianMetric I M) (_ : M) => (0 :
        TangentSpace I _ →L[ℝ] TangentSpace I _ →L[ℝ] ℝ)) g α i j y = 0 := rfl

/-- **The zero operator is not strictly parabolic.**

The zero metric right-hand side `F := fun _ _ => 0` (a symmetric tensor field) does **not**
have a principal symbol at any metric `g₀`: `∃ σ, HasPrincipalSymbol (fun _ _ => 0) g₀ σ`
is **false**.

*Argument.*  Suppose `HasPrincipalSymbol (fun _ _ => 0) g₀ σ`, witnessed by a chart second
order part `P` (with first-order remainder `R`) and the symbol identification.  Pick any
base point `x`, any nonzero covector `ξ`, and any **nonzero** symmetric fibre form `t`
(such a `t` exists in positive dimension).  Realise `g₀ ⊕ s·(symbol test perturbation)`
near `x` by a family `gfam` (`hfam`).  The chart component of the *zero* operator is the
constant `0`, so its directional derivative vanishes:
`0 = deriv (fun s => 0) 0 = P hξt x i j y₀ + R hξt x i j y₀`.  The symbol test perturbation
`hξt` has vanishing component value and first chart derivatives at `y₀ = extChartAt I x x`
(`symbolTestPerturbation_apply_self`, `partialDeriv_symbolTestPerturbation_self`), so the
first-order remainder vanishes there (`IsFirstOrderInPerturbation`):
`R hξt x i j y₀ = 0`, whence `P hξt x i j y₀ = 0`.  The symbol identification then forces
`(σ x ξ t)(e_i, e_j) = −P hξt x i j y₀ = 0` for all `i, j`, i.e. `σ x ξ t = 0`.  But strict
parabolicity gives `σ x ξ t = −|ξ|²_{g₀} · t` with `|ξ|²_{g₀} > 0` and `t ≠ 0`, so
`σ x ξ t ≠ 0` — a contradiction.

The realisability hypothesis `hfam` (a family of genuine positive-definite metrics moving
along the symbol test perturbation to first order near `x`) is the mild geometric input;
it holds because a small chart-cutoff symmetric perturbation of a metric is again a
metric.  The same argument rejects any first-order, zeroth-order or anisotropic operator,
whose chart `∂²h`-coefficient's symbol is not `−|ξ|²_{g₀} · id`. -/
theorem not_hasPrincipalSymbol_zero_operator [I.Boundaryless]
    (g₀ : SmoothRiemannianMetric I M) (x : M) {ξ : E} (hξ : ξ ≠ 0)
    {t : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ}
    (ht : ∀ v w, t v w = t w v) (ht0 : t ≠ 0)
    (hfam : ∀ (h : ChartMetricPerturbation E),
      ∃ gfam : ℝ → SmoothRiemannianMetric I M,
        IsMetricPerturbationFamily (I := I) g₀ x h gfam) :
    ¬ ∃ σ : DifferentialGeometry.PDE.DeTurck.TensorSymbol (E := E) I M,
        HasPrincipalSymbol (I := I)
          (fun (_ : SmoothRiemannianMetric I M) (_ : M) => (0 :
            TangentSpace I _ →L[ℝ] TangentSpace I _ →L[ℝ] ℝ)) g₀ σ := by
  rintro ⟨σ, P, ⟨R, hR_first, hsplit⟩, hσ⟩
  set hξt : ChartMetricPerturbation E := symbolTestPerturbation (I := I) x x ξ t ht with hξt_def
  have hy_int : extChartAt I x x ∈ interior (extChartAt I x).target := by
    have hx_src : x ∈ (extChartAt I x).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact mem_chart_source H x
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) x
      ((extChartAt I x).map_source hx_src)
  obtain ⟨gfam, hfam0, hfam_deriv, hfam_smooth, hfam_jet1, hfam_jet2⟩ := hfam hξt
  have hσ_zero : ∀ i j : Fin (Module.finrank ℝ E),
      (σ x ξ t) ((chartModelBasis E) i) ((chartModelBasis E) j) = 0 := by
    intro i j
    have hsymbol := (hσ x ξ hξ t ht).1 ht i j
    have hderiv0 :
        deriv (fun s : ℝ =>
          chartFComponentOnE (I := I)
            (fun (_ : SmoothRiemannianMetric I M) (_ : M) => (0 :
              TangentSpace I _ →L[ℝ] TangentSpace I _ →L[ℝ] ℝ)) (gfam s) x i j
            (extChartAt I x x)) 0 = 0 := by
      simp only [chartFComponentOnE_zero_operator]
      exact deriv_const 0 0
    have hsplit' := hsplit x hξt gfam ⟨hfam0, hfam_deriv, hfam_smooth, hfam_jet1, hfam_jet2⟩
      i j hy_int
    rw [hderiv0] at hsplit'
    have hR0 : R hξt x i j (extChartAt I x x) = 0 :=
      hR_first x hξt i j hy_int
        (fun a b => symbolTestPerturbation_apply_self (I := I) x x ξ t ht a b)
        (fun p a b => partialDeriv_symbolTestPerturbation_self (I := I) x x ξ t ht p a b)
    have hP0 : P hξt x i j (extChartAt I x x) = 0 := by
      rw [hR0, add_zero] at hsplit'
      exact hsplit'.symm
    rw [hP0] at hsymbol
    linarith [hsymbol]
  have hσt_zero : σ x ξ t = 0 := by
    refine LinearMap.ext_basis (chartModelBasis E) (chartModelBasis E) (fun i j => ?_)
    exact hσ_zero i j
  have hσt_isotropic := (hσ x ξ hξ t ht).2.1
  rw [hσt_zero] at hσt_isotropic
  have hnorm_pos := (hσ x ξ hξ t ht).2.2
  have htneg : (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ)
      • t = 0 := hσt_isotropic.symm
  have hcoeff_ne : (- DifferentialGeometry.PDE.DeTurck.metricCovectorNormSq (I := I) g₀ x ξ)
      ≠ 0 := by
    rw [neg_ne_zero]
    exact ne_of_gt hnorm_pos
  exact ht0 ((smul_eq_zero.mp htneg).resolve_left hcoeff_ne)

end RicciFlow
end PDE
end DifferentialGeometry

end
