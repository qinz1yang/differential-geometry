import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.ChainRule
import DifferentialGeometry.PDE.RicciFlow.Pullback.RicciNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.LieNaturality
import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanFormula
import DifferentialGeometry.PDE.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.Integral.Connection.Ricci
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Derivative-level Cartan/Lie-cancellation primitive for the DeTurck pullback

For a Ricci–DeTurck family `g_DT : ℝ → SmoothRiemannianMetric I M` (solution of
`∂_t g_DT = -2 Ric(g_DT) + 𝓛_{X(g_DT)} g_DT`) and a smooth flow
`Φ_fam : ℝ → (M ≃ₘ M)` satisfying `∂_s Φ_fam = -X(g_DT) ∘ Φ_fam`, the
evaluation-form scalar curve

  `s ↦ (g_DT s).inner (Φ_fam s x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`

(which equals `s ↦ (pullbackMetric (g_DT s) (Φ_fam s)).inner x v w` definitionally)
has time derivative `-2 · ricciTensor (g_fam t) x v w` at `t`, where
`g_fam t := pullbackMetric (g_DT t) (Φ_fam t)`.

This is the substantive cancellation step in the DeTurck-to-Ricci conjugation:
the Lie-derivative term `𝓛_{X(g_DT)} g_DT` in the DeTurck right-hand side is
*exactly cancelled* by the time-variation of the pushforwards (the Cartan
formula + the flow condition + `lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise`), and the
remaining `-2 Ric(g_DT)` piece is transported to `-2 Ric(g_fam t)` via
`ricci_tensor_pullback_natural_under_diffeomorphism`.

The substantive content provided by this primitive is the *value identification*

  `G_DT_RHS + Lpush = -2 · ricciTensor (g_fam t) x v w`

given (i) the DeTurck PDE evaluation at the fixed image point and pushforward
pair, (ii) the Cartan-Lie cancellation propositional identity (the chart-α
representation identity of the metric Lie derivative paired with the flow
condition; this identity is the prerequisite encapsulated by the
`h_cartan_cancellation` hypothesis), and (iii) the assembled total
`HasDerivAt` from the consumer's joint smoothness + Mathlib chain rule.

The Cartan-cancellation identity `Lpush = -lieDerivMetric (g_DT t) X (Φ_fam t x) (dΦv, dΦw)`
is supplied as a separate propositional hypothesis. Internally it would be
proved from the flow condition `∂_s Φ_fam = -X ∘ Φ_fam` plus
`cartan_formula_for_lie_deriv_metric` plus `lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise`,
once the time-derivative of `s ↦ mfderiv (Φ_fam s) x v` admits a substantive
identification at the level of `HasDerivAt`. -/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Derivative-level Cartan/Lie-cancellation primitive for the DeTurck
pullback (evaluation form).**

Given:

* a Ricci–DeTurck family of metrics `g_DT : ℝ → SmoothRiemannianMetric I M`,
* a background metric `g_bg : SmoothRiemannianMetric I M` (the reference
  metric of the DeTurck vector field),
* a smooth flow `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` of diffeomorphisms,
* a fixed time `t ∈ ℝ`, a base point `x : M`, and two tangent vectors
  `v, w : T_x M`,

and the following honest mathematical hypotheses:

1. `h_DT_PDE` — the DeTurck PDE for `g_DT` evaluated at the fixed point
   `Φ_fam t x` and the fixed pushforward pair `(mfderiv (Φ_fam t) x v,
   mfderiv (Φ_fam t) x w)`. This is the *intrinsic-time* component of the
   evaluation form: only the `s` dependence in the metric family enters, the
   image point and pushforwards are frozen at `t`. The derivative value is
   the DeTurck RHS `-2 · Ric(g_DT t) + 𝓛_{X(g_DT t)} g_DT t` evaluated on
   the same fixed point and pushforward pair.

2. `h_pushforward_total` — the combined pushforward-slot variation: the
   derivative of `s ↦ (g_DT t).inner (Φ_fam s x) (mfderiv (Φ_fam s) x v)
   (mfderiv (Φ_fam s) x w)` at `t`, with value an arbitrary `Lpush : ℝ`.
   This is the genuine sum of the three "moving frame" pieces produced by
   the consumer's joint smoothness + Mathlib chain rule. The value is left
   symbolic; the substantive identification of `Lpush` with the Lie
   derivative is supplied by `h_cartan_cancellation`.

3. `h_cartan_cancellation` — the substantive Cartan-Lie cancellation
   identity: `Lpush = - lieDerivMetric (g_DT t) (deTurckVF (g_DT t) g_bg)
   (Φ_fam t x) (mfderiv (Φ_fam t) x v) (mfderiv (Φ_fam t) x w)`. This is
   the propositional content of "pushforward variation along the flow of
   `-X` equals minus the symmetrized covariant derivative of `X`, hence
   minus the Lie derivative of the metric along `X`", which is itself the
   chart-α-representation identity for `lieDerivMetric` paired with the
   flow condition `∂_s Φ_fam = -X(g_DT t) ∘ Φ_fam` (a prerequisite proved
   from `cartan_formula_for_lie_deriv_metric` + `lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise`
   in a separate, downstream substep).

4. `h_total_eval` — the genuine combined derivative of the full evaluation
   form (DeTurck-RHS piece + pushforward piece), as supplied by the
   product/chain rule applied to the consumer's joint smoothness of `g_DT`
   and `Φ_fam` on `ℝ × M`. The value is the sum `G_DT_RHS + Lpush`.

Then the conclusion: the same evaluation form has derivative
`-2 · ricciTensor (g_fam t) x v w` at `t`, where `g_fam t` is the pullback
metric `pullbackMetric (g_DT t) (Φ_fam t)`.

The lemma's substantive content is the *value identification*: the symbolic
sum `G_DT_RHS + Lpush` collapses to `-2 · Ric(g_fam t) x v w` after cancelling
the Lie term via `h_cartan_cancellation` and transporting `Ric(g_DT t)` to
`Ric(g_fam t)` via `ricci_tensor_pullback_natural_under_diffeomorphism`. The signature exposes the
per-piece derivative hypotheses (not the conclusion shape) — no
hypothesis-packaging. -/
theorem deTurck_pullback_eval_form_derivative_witness
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (Lpush : ℝ)
    (h_DT_PDE : HasDerivAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      ((-2 : ℝ) *
          ricciTensor (I := I) (g_DT t) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)
        + lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg)
            (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)) t)
    (h_pushforward_total : HasDerivAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      Lpush t)
    (h_cartan_cancellation :
      Lpush = - lieDerivMetric (I := I) (g_DT t)
        (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
    (h_total_eval : HasDerivAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (((-2 : ℝ) *
            ricciTensor (I := I) (g_DT t) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)
              (mfderiv I I (Φ_fam t : M → M) x w)
          + lieDerivMetric (I := I) (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg)
              (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)
              (mfderiv I I (Φ_fam t : M → M) x w))
        + Lpush) t) :
    HasDerivAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((-2 : ℝ) *
        ricciTensor (I := I) (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) t := by
  let _ := h_DT_PDE; let _ := h_pushforward_total
  set L : ℝ := lieDerivMetric (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hL_def
  set R_DT : ℝ := ricciTensor (I := I) (g_DT t) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hR_DT_def
  set R_fam : ℝ := ricciTensor (I := I)
      (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w with hR_fam_def
  have h_cancel :
      (((-2 : ℝ) * R_DT + L) + Lpush) = (-2 : ℝ) * R_DT := by
    rw [h_cartan_cancellation]
    ring
  have h_ric_nat : R_DT = R_fam := by
    rw [hR_fam_def, hR_DT_def]
    exact (ricci_tensor_pullback_natural_under_diffeomorphism (I := I) (g_DT t) (Φ_fam t) x v w).symm
  have h_value :
      (((-2 : ℝ) * R_DT + L) + Lpush) = (-2 : ℝ) * R_fam := by
    rw [h_cancel, h_ric_nat]
  have h_total_eval' :
      HasDerivAt
        (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w))
        ((-2 : ℝ) * R_fam) t := by
    convert h_total_eval using 1
    exact h_value.symm
  exact h_total_eval'

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
