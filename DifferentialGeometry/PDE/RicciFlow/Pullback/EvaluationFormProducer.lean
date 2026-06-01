import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.PDE.RicciFlow.Pullback.ChainRule
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! # Multivariable chain-rule producer for the pullback evaluation form

The time-derivative chain rule for the pullback metric
(`pullback_time_derivative_chain_rule`) and the additive decomposition
(`pullback_metric_derivative_decomposition`) each consume a single substantive
hypothesis — the *evaluation-form total derivative* `h_chain_eval` /
`h_total_eval`, i.e. a `HasDerivAt` witness for the scalar curve

  `s ↦ (g_fam s).inner (Φ_fam s x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`

with the appropriate value.  Those theorems take the witness as input; this file
*produces* it from the genuine smoothness data of the inputs.

## The structural observation

For each `s`, the tangent space `TangentSpace I (Φ_fam s x)` is *definitionally*
the model fibre `E` (Mathlib defines `TangentSpace I _ := E`).  Consequently the
three `s`-dependent ingredients of the evaluation form all live in fixed normed
spaces:

* `B s := (g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ`  — the metric slot,
  carrying both the intrinsic time variation of `g_fam` and the motion of the
  evaluation base point `Φ_fam s x`;
* `a s := mfderiv I I (Φ_fam s) x v : E`  — the first pushforward slot;
* `b s := mfderiv I I (Φ_fam s) x w : E`  — the second pushforward slot.

The evaluation form is then the genuine trilinear evaluation `B s (a s) (b s)`.
By Mathlib's `HasDerivAt.clm_apply` (applied twice) the total derivative is the
*sum of the three per-slot derivatives*

  `B' (a t) (b t)  +  (B t) a' (b t)  +  (B t) (a t) b'`,

which is precisely the multivariable chain rule.  No flow, generator, or
curvature hypotheses appear: the producer is parametric in abstract smooth
`g_fam` / `Φ_fam`, and the actual joint smoothness of a concrete metric family
(supplying the slot-wise `HasDerivAt` data) is furnished downstream.

## What this file delivers

* `trilinear_eval_hasDerivAt` / `…WithinAt` — the abstract model-space core:
  three slot `HasDerivAt`s ⇒ the trilinear-evaluation `HasDerivAt`.
* `pullback_eval_form_hasDerivAt_of_slots` / `…WithinAt` — the geometric
  evaluation-form producer (explicit three-summand value), parametric in
  `g_fam` / `Φ_fam`.
* `pullback_eval_form_total_hasDerivAt` — the `h_total_eval` shape
  (value `G' + A' + B'`) for `pullback_metric_derivative_decomposition`.
* `pullback_eval_form_chain_hasDerivAt` — the `h_chain_eval` shape
  (value `G' + L'`) for `pullback_time_derivative_chain_rule`.
* `pullback_metric_chain_rule_of_slots` — the full capstone: from the three
  slot derivatives directly to the bundled `pullbackMetric` conclusion.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Trilinear evaluation chain rule (`HasDerivWithinAt`).**

For curves `B : ℝ → (E →L[ℝ] E →L[ℝ] ℝ)`, `a, b : ℝ → E` differentiable within
`S` at `t`, the scalar curve `s ↦ B s (a s) (b s)` has within-set derivative

  `(B' (a t) (b t) + B t a' (b t)) + B t (a t) b'`.

Proved by applying Mathlib's `HasDerivWithinAt.clm_apply` twice: first to the
pair `(B, a)` giving the inner application `s ↦ (B s) (a s) : E →L[ℝ] ℝ`, then to
the resulting curve paired with `b`. -/
theorem trilinear_eval_hasDerivWithinAt
    {B : ℝ → (E →L[ℝ] E →L[ℝ] ℝ)} {a b : ℝ → E} {S : Set ℝ} {t : ℝ}
    {B' : E →L[ℝ] E →L[ℝ] ℝ} {a' b' : E}
    (hB : HasDerivWithinAt B B' S t) (ha : HasDerivWithinAt a a' S t)
    (hb : HasDerivWithinAt b b' S t) :
    HasDerivWithinAt (fun s : ℝ => B s (a s) (b s))
      ((B' (a t) (b t) + B t a' (b t)) + B t (a t) b') S t := by
  have step1 := hB.clm_apply ha
  have step2 := step1.clm_apply hb
  convert step2 using 1

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Trilinear evaluation chain rule (`HasDerivAt`).**

Strict (unrestricted) variant of `trilinear_eval_hasDerivWithinAt`: for curves
`B : ℝ → (E →L[ℝ] E →L[ℝ] ℝ)`, `a, b : ℝ → E` differentiable at `t`, the scalar
curve `s ↦ B s (a s) (b s)` has derivative
`(B' (a t) (b t) + B t a' (b t)) + B t (a t) b'`. -/
theorem trilinear_eval_hasDerivAt
    {B : ℝ → (E →L[ℝ] E →L[ℝ] ℝ)} {a b : ℝ → E} {t : ℝ}
    {B' : E →L[ℝ] E →L[ℝ] ℝ} {a' b' : E}
    (hB : HasDerivAt B B' t) (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s : ℝ => B s (a s) (b s))
      ((B' (a t) (b t) + B t a' (b t)) + B t (a t) b') t := by
  have step1 := hB.clm_apply ha
  have step2 := step1.clm_apply hb
  convert step2 using 1

/-- **Pullback evaluation-form producer (`HasDerivAt`, explicit three-summand
value).**

Given the per-slot derivative witnesses of the pullback evaluation form:

* `hB` — the metric slot `s ↦ (g_fam s).inner (Φ_fam s x)` (typed into
  `E →L[ℝ] E →L[ℝ] ℝ`) has derivative `B'` at `t`; this carries *both* the
  intrinsic time variation of `g_fam` and the motion of the base point
  `Φ_fam s x`;
* `ha` — the first pushforward slot `s ↦ mfderiv I I (Φ_fam s) x v` (typed into
  `E`) has derivative `a'`;
* `hb` — the second pushforward slot `s ↦ mfderiv I I (Φ_fam s) x w` (typed into
  `E`) has derivative `b'`,

the evaluation-form scalar curve has derivative

  `(B' (dΦ_t v) (dΦ_t w)  +  (g_fam t).inner (Φ_fam t x) a' (dΦ_t w))
      +  (g_fam t).inner (Φ_fam t x) (dΦ_t v) b'`

at `t`, where `dΦ_t v = mfderiv I I (Φ_fam t) x v`.  This is the multivariable
chain rule; the three summands are the metric/base-point slot, the first
pushforward slot, and the second pushforward slot respectively. -/
theorem pullback_eval_form_hasDerivAt_of_slots
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t) :
    HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((B' (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
          + ((g_fam t).inner (Φ_fam t x)) a' (mfderiv I I (Φ_fam t : M → M) x w))
        + ((g_fam t).inner (Φ_fam t x)) (mfderiv I I (Φ_fam t : M → M) x v) b') t :=
  trilinear_eval_hasDerivAt hB ha hb

/-- **Pullback evaluation-form producer (`HasDerivWithinAt`, explicit
three-summand value).**

Within-set variant of `pullback_eval_form_hasDerivAt_of_slots`, for consumers
whose time domain is a set `S` (e.g. `Set.Ici 0`). -/
theorem pullback_eval_form_hasDerivWithinAt_of_slots
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    {S : Set ℝ} (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (hB : HasDerivWithinAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' S t)
    (ha : HasDerivWithinAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' S t)
    (hb : HasDerivWithinAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' S t) :
    HasDerivWithinAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((B' (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
          + ((g_fam t).inner (Φ_fam t x)) a' (mfderiv I I (Φ_fam t : M → M) x w))
        + ((g_fam t).inner (Φ_fam t x)) (mfderiv I I (Φ_fam t : M → M) x v) b') S t :=
  trilinear_eval_hasDerivWithinAt hB ha hb

/-- **Producer of the `h_total_eval` witness** (value `G' + A' + B'`).

Given the three slot derivatives (`hB`, `ha`, `hb`) and the value
identifications

* `hG' : G' = B' (dΦ_t v) (dΦ_t w)`              (metric / base-point slot),
* `hA' : A' = (g_fam t).inner (Φ_fam t x) a' (dΦ_t w)`   (first pushforward slot),
* `hB_val : B'' = (g_fam t).inner (Φ_fam t x) (dΦ_t v) b'` (second pushforward slot),

the evaluation-form scalar curve has derivative `G' + A' + B''` at `t` — the
exact `h_total_eval` hypothesis of `pullback_metric_derivative_decomposition`. -/
theorem pullback_eval_form_total_hasDerivAt
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' A' B'' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hA' : A' = ((g_fam t).inner (Φ_fam t x)) a'
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hB_val : B'' = ((g_fam t).inner (Φ_fam t x))
      (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + A' + B'') t := by
  rw [hG', hA', hB_val]
  exact pullback_eval_form_hasDerivAt_of_slots g_fam Φ_fam t x v w B' a' b' hB ha hb

/-- **Producer of the `h_chain_eval` witness** (value `G' + L'`).

Given the three slot derivatives and the value identifications

* `hG' : G' = B' (dΦ_t v) (dΦ_t w)`     (intrinsic time / base-point piece),
* `hL' : L' = (g_fam t).inner (Φ_fam t x) a' (dΦ_t w)
        + (g_fam t).inner (Φ_fam t x) (dΦ_t v) b'`   (grouped pushforward piece),

the evaluation-form scalar curve has derivative `G' + L'` at `t` — the exact
`h_chain_eval` hypothesis of `pullback_time_derivative_chain_rule`. -/
theorem pullback_eval_form_chain_hasDerivAt
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' L' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hL' : L' = ((g_fam t).inner (Φ_fam t x)) a'
        (mfderiv I I (Φ_fam t : M → M) x w)
      + ((g_fam t).inner (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t := by
  have hkey := pullback_eval_form_hasDerivAt_of_slots g_fam Φ_fam t x v w B' a' b' hB ha hb
  have hval :
      (B' (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
          + ((g_fam t).inner (Φ_fam t x)) a' (mfderiv I I (Φ_fam t : M → M) x w))
        + ((g_fam t).inner (Φ_fam t x)) (mfderiv I I (Φ_fam t : M → M) x v) b'
      = G' + L' := by
    rw [hG', hL']; ring
  rwa [hval] at hkey

/-- **Full pullback time-derivative chain rule from slot derivatives.**

From the three slot derivatives of the pullback evaluation form and the value
identifications of the intrinsic-time piece `G'` and the grouped pushforward
piece `L'`, conclude that the *bundled* pullback inner product
`s ↦ (pullbackMetric (g_fam s) (Φ_fam s)).inner x v w` has derivative `G' + L'`
at `t`.  This is the conclusion of `pullback_time_derivative_chain_rule` with the
substantive `h_chain_eval` hypothesis now *produced* internally from the
smoothness inputs. -/
theorem pullback_metric_chain_rule_of_slots
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' L' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hL' : L' = ((g_fam t).inner (Φ_fam t x)) a'
        (mfderiv I I (Φ_fam t : M → M) x w)
      + ((g_fam t).inner (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  pullback_time_derivative_chain_rule g_fam Φ_fam t x v w G' L'
    (pullback_eval_form_chain_hasDerivAt g_fam Φ_fam t x v w B' a' b' G' L'
      hB ha hb hG' hL')

/-- **Full pullback time-derivative chain rule from slot derivatives
(three-summand value).**

Variant of `pullback_metric_chain_rule_of_slots` exposing the value as the
three-summand sum `G' + A' + B''` (the `h_total_eval` shape of
`pullback_metric_derivative_decomposition`), produced from the slot derivatives
and the three per-slot value identifications. -/
theorem pullback_metric_chain_rule_of_slots_total
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (B' : E →L[ℝ] E →L[ℝ] ℝ) (a' b' : E)
    (G' A' B'' : ℝ)
    (hB : HasDerivAt
      (fun s : ℝ => ((g_fam s).inner (Φ_fam s x) : E →L[ℝ] E →L[ℝ] ℝ)) B' t)
    (ha : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x v :
        TangentSpace I (Φ_fam s x)) : E)) a' t)
    (hb : HasDerivAt
      (fun s : ℝ => ((mfderiv I I (Φ_fam s : M → M) x w :
        TangentSpace I (Φ_fam s x)) : E)) b' t)
    (hG' : G' = B' (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hA' : A' = ((g_fam t).inner (Φ_fam t x)) a'
      (mfderiv I I (Φ_fam t : M → M) x w))
    (hB_val : B'' = ((g_fam t).inner (Φ_fam t x))
      (mfderiv I I (Φ_fam t : M → M) x v) b') :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + A' + B'') t :=
  pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w
    (pullback_eval_form_total_hasDerivAt g_fam Φ_fam t x v w B' a' b' G' A' B''
      hB ha hb hG' hA' hB_val)

end DifferentialGeometry.PDE.RicciFlow.Pullback
