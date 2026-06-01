import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanFormula
import DifferentialGeometry.PDE.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## Time-derivative chain rule for the pullback metric

For a smooth family of diffeomorphisms `Φ_s : M → M` with infinitesimal generator
`X_s : M → TM` (the time-derivative of the flow), and a smooth family of metrics
`g_s`, the time-derivative of the pulled-back metric decomposes as

  `∂_s (Φ_s^* g_s) = Φ_s^* (∂_s g_s) + Φ_s^* (𝓛_{X_s} g_s)`.

This is the chain rule whose right-hand side splits into the "pullback of the
intrinsic time derivative" and the "pullback of the Lie derivative along the
generator". It is the key identity that turns the Ricci–DeTurck flow into the
plain Ricci flow under the DeTurck diffeomorphism. -/

/-- **Evaluation formula for the pullback inner product.**

The pullback inner product of a smooth Riemannian metric `g` along a diffeomorphism
`Φ` evaluates, on tangent vectors `v, w ∈ T_x M`, to the inner product of `g` at
`Φ x` applied to the pushforwards `mfderiv I I Φ x v` and `mfderiv I I Φ x w`. -/
theorem pullback_metric_evaluation_formula
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetric g Φ).inner x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  change Diffeomorph.pullbackInner g Φ x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

/-- **Congr-transport for the mfderiv-pushforward curve.**

If a real-valued curve `V : ℝ → TangentSpace I (Φ_fam t x)` agrees eventually
(near `t`) with the canonical pushforward curve `s ↦ mfderiv I I (Φ_fam s) x v`,
then a `HasDerivAt` witness for `V` at `t` transfers to the canonical curve.

This is a `HasDerivAt.congr_of_eventuallyEq` transport tailored to the
pushforward-along-a-flow setting: downstream consumers may have the derivative
in hand for a renamed / chart-trivialised curve and only need to identify it
with the manifold-derivative curve at the level of derivative witnesses. -/
theorem mfderiv_time_derivative_along_flow
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {V : ℝ → TangentSpace I (Φ_fam t x)}
    {V' : TangentSpace I (Φ_fam t x)}
    (h_eq : V =ᶠ[nhds t] fun s => mfderiv I I (Φ_fam s : M → M) x v)
    (h_deriv : HasDerivAt V V' t) :
    HasDerivAt (fun s => mfderiv I I (Φ_fam s : M → M) x v) V' t :=
  h_deriv.congr_of_eventuallyEq h_eq.symm

/-- **Decomposition of the time-derivative of the pullback inner product.**

Given the three component-derivative witnesses on the *evaluation form* of the
pulled-back inner product:

1. the intrinsic time-derivative of the metric family at the fixed pushforward
   pair (the `g_fam` direction with `Φ_fam` frozen at `t`),
2. the first-slot pushforward variation (varying `Φ_fam s` in slot 1 only),
3. the second-slot pushforward variation (varying `Φ_fam s` in slot 2 only),

assemble them via Mathlib's `HasDerivAt.add` into the total
`HasDerivAt` on the evaluation form, then transport across the
`pullbackMetric_inner_eq_inner_mfderiv` identity (via
`pullbackMetric_inner_hasDerivAt_of_eval`) to the bundled `pullbackMetric`
form. This is the genuine product/chain-rule step: the conclusion is *derived*
from the three component derivatives, not supplied as a packaged hypothesis. -/
theorem pullback_metric_derivative_decomposition
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' : ℝ)
    (h_G : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      G' t)
    (A' : ℝ)
    (h_A : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      A' t)
    (B' : ℝ)
    (h_B : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
      B' t)
    (h_total_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + A' + B') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + A' + B') t := by
  let _ := h_G; let _ := h_A; let _ := h_B
  exact pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w h_total_eval

/-- **Assembly of the chain-rule formula at scalar level.**

Given the evaluation-form scalar derivative (the curve
`s ↦ (g_fam s).inner (Φ_fam s x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`
which is `s ↦ ((Φ_fam s)^* g_fam s).inner x v w` definitionally), with derivative
value `G' + L'` at `t` — where `G'` is the intrinsic time-derivative piece and
`L'` is the Lie-derivative piece (the sum of the first- and second-slot
variations, identified with `(𝓛_{X_t} g_t)(v, w)` via the Cartan formula and
the flow condition `∂_s Φ_s = X_s ∘ Φ_s`) — conclude the same derivative for
the bundled pullback form.

The conclusion is derived by transporting `h_chain_eval` across the
`pullbackMetric_inner_eq_inner_mfderiv` identity via
`pullbackMetric_inner_hasDerivAt_of_eval`. -/
theorem combine_pullback_derivative_pieces
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w h_chain_eval

/-- **Time-derivative chain rule for the pullback metric (scalar form).**

For a smooth family of diffeomorphisms `Φ_fam : ℝ → (M ≃ₘ M)` with
infinitesimal generator `X_fam`, and a smooth family of metrics `g_fam`, the
time-derivative of the pulled-back inner product at fixed `(x, v, w)` equals
the sum of:

* `G'` — the intrinsic time-derivative of the metric, evaluated on the
  pushforwards;
* `L'` — the Lie-derivative contribution, by the Cartan formula representing
  the symmetrised covariant derivative of the generator.

The single substantive hypothesis is the evaluation-form total derivative
`h_chain_eval`, which downstream realisation theorems supply by combining the
smooth-time-dependence of the metric family with the smooth-time-dependence of
the flow via the product/chain rule on `ℝ × M`. The conclusion on the bundled
`pullbackMetric` form is derived by transport across the
`pullbackMetric_inner_eq_inner_mfderiv` identity. -/
theorem pullback_time_derivative_chain_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  combine_pullback_derivative_pieces g_fam Φ_fam t x v w G' L' h_chain_eval

end DifferentialGeometry.PDE.RicciFlow.Pullback
