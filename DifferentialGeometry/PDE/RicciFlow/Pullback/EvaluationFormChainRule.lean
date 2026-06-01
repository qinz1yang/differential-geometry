import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullback
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormProducer
import DifferentialGeometry.PDE.RicciFlow.Pullback.ChainRule
import DifferentialGeometry.PDE.RicciFlow.Pullback.TimeDerivativeChainRule
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Discharging the chain-rule regularity hypothesis for the pullback assembly

The Hamilton–DeTurck pullback assembly differentiates the evaluation-form scalar
curve

  `s ↦ (g_DT s).inner (Φ_fam s x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`

(definitionally `s ↦ (pullbackMetric (g_DT s) (Φ_fam s)).inner x v w`) in time and
consumes a single substantive *regularity hypothesis* — the joint within-set
derivative of this curve (`h_total_eval` of `hamilton_deturck_pullback_solves_ricci_flow`,
equivalently `h_chain_eval` of `pullback_time_derivative_chain_rule`).

This file **produces** that joint derivative from the genuine separable inputs,
*without* assuming joint `C^∞` on `ℝ × M`.  The scalar two-variable evaluation map

    `Q (s₁, s₂) := (g_DT s₁).inner (Φ_fam s₂ x) (mfderiv (Φ_fam s₂) x v)
                     (mfderiv (Φ_fam s₂) x w)`

has the evaluation form as its *diagonal* `Q (s, s)`, and the inputs are:

* the **metric slot** = first partial `s₁ ↦ Q (s₁, t)` (the *whole* geometric
  data — image point and pushforwards — frozen at `t`, only the metric family
  varying) — exactly the parabolic solution's pointwise time derivative
  `deTurck_metric_slot_hasDerivWithinAt`;
* the **moving-geometry slot** = second partial `s₂ ↦ Q (t, s₂)` (the metric
  frozen at `g_DT t`, the *whole* geometric data — image point `Φ_fam s₂ x` *and*
  pushforwards — moving along the flow; equivalently the time derivative of the
  fixed-metric pull-back `((Φ_fam s₂)^*(g_DT t)).inner x v w`).  Because the image
  point genuinely moves, this is the flow's *smooth-in-initial-condition* content,
  supplied as a separable hypothesis from the variational track — **not** the
  frozen-base variational slot lemma;
* the **joint Fréchet differentiability at a single point**
  `HasFDerivWithinAt Q Q' ((Ici 0) ×ˢ univ) (t, t)`.  This is a strictly
  separable, single-point analytic fact about a real-valued function of two real
  variables — far weaker than (and never derived from) any joint-`C^∞`-on-`ℝ × M`
  hypothesis, and it is the genuine analytic content connecting the two partial
  derivatives to the diagonal derivative.

## The diagonal chain rule

For a jointly Fréchet-differentiable `Q`, the diagonal restriction `s ↦ Q (s, s)`
has derivative the sum of the two partials `Q'(1,0) + Q'(0,1)` (compose `Q` with
the diagonal map `s ↦ (s, s)`, whose within-set derivative is `(1, 1)`, then
expand `Q'(1,1) = Q'(1,0) + Q'(0,1)` by linearity).  The two partials are then
**identified** with the two supplied slot derivatives — not assumed equal — by
uniqueness of the within-set derivative on `Ici 0` (`uniqueDiffOn_Ici`): the
metric-slot derivative `s₁ ↦ Q(s₁, t)` is the partial `Q'(1,0)`, and the
moving-geometry slot derivative `s₂ ↦ Q(t, s₂)` is the partial `Q'(0,1)`.

Consequently the diagonal derivative equals
`(metric-slot value) + (moving-geometry-slot value)`, exactly the additive value
shape that `hamilton_deturck_pullback_solves_ricci_flow` expects, and hence the
chain-rule hypothesis `h_chain_eval` of `pullback_time_derivative_chain_rule` is
discharged.

No `sorry`/`axiom`/new `class`, no `HasLocallyConstantChartAt`-style hypothesis, and
no joint-`C^∞`-on-`ℝ × M` hypothesis appears anywhere in this file.  The headline
derivative is *derived* from the two slot derivatives and the single-point joint
Fréchet differentiability — never supplied as a packaged conclusion.
-/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Abstract diagonal chain rule (single-point joint Fréchet hypothesis).**

If `Q : ℝ × ℝ → ℝ` has the within-set Fréchet derivative `Q'` along
`(Ici 0) ×ˢ univ` at `(t, t)`, then the diagonal curve `s ↦ Q (s, s)` has the
within-set derivative `Q' (1, 0) + Q' (0, 1)` along `Ici 0` at `t`.

The proof composes `Q` with the diagonal map `s ↦ (s, s)` (whose within-set
derivative is `(1, 1)`, mapping `Ici 0` into `(Ici 0) ×ˢ univ`) and expands the
value `Q' (1, 1) = Q' (1, 0) + Q' (0, 1)` by linearity of `Q'`. -/
theorem evalForm_diagonal_hasDerivWithinAt_of_jointFDeriv
    (Q : ℝ × ℝ → ℝ) (t : ℝ) (Q' : (ℝ × ℝ) →L[ℝ] ℝ)
    (hQ : HasFDerivWithinAt Q Q' ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt (fun s : ℝ => Q (s, s)) (Q' (1, 0) + Q' (0, 1))
      (Set.Ici (0 : ℝ)) t := by
  have hδ : HasDerivWithinAt (fun s : ℝ => (s, s)) ((1 : ℝ), (1 : ℝ))
      (Set.Ici (0 : ℝ)) t :=
    (hasDerivWithinAt_id t (Set.Ici (0 : ℝ))).prodMk
      (hasDerivWithinAt_id t (Set.Ici (0 : ℝ)))
  have hmaps : Set.MapsTo (fun s : ℝ => (s, s)) (Set.Ici (0 : ℝ))
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) := fun s hs => ⟨hs, Set.mem_univ _⟩
  have hcomp : HasDerivWithinAt (Q ∘ fun s : ℝ => (s, s)) (Q' ((1 : ℝ), (1 : ℝ)))
      (Set.Ici (0 : ℝ)) t :=
    HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (f := fun s : ℝ => (s, s)) t hQ hδ
      hmaps (by simp)
  have hval : Q' ((1 : ℝ), (1 : ℝ)) = Q' (1, 0) + Q' (0, 1) := by
    rw [← map_add]; congr 1; ext <;> simp
  rwa [hval] at hcomp

/-- **First partial (frozen second variable).**

The first partial `Q' (1, 0)` of a jointly Fréchet-differentiable `Q` at `(t, t)`
along `(Ici 0) ×ˢ univ` is the within-set derivative of the frozen-second-
variable curve `s₁ ↦ Q (s₁, t)` along `Ici 0` at `t`.  Composing `Q` with the
embedding `s₁ ↦ (s₁, t)` (within-set derivative `(1, 0)`, mapping into the product
set: the moving first component stays in `Ici 0` and the frozen second component
lies in `univ`). -/
theorem evalForm_jointFDeriv_partial_fst
    (Q : ℝ × ℝ → ℝ) (t : ℝ) (Q' : (ℝ × ℝ) →L[ℝ] ℝ)
    (hQ : HasFDerivWithinAt Q Q' ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt (fun s : ℝ => Q (s, t)) (Q' (1, 0)) (Set.Ici (0 : ℝ)) t := by
  have hε : HasDerivWithinAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ))
      (Set.Ici (0 : ℝ)) t :=
    (hasDerivWithinAt_id t (Set.Ici (0 : ℝ))).prodMk
      (hasDerivWithinAt_const t (Set.Ici (0 : ℝ)) t)
  have hmaps : Set.MapsTo (fun s : ℝ => (s, t)) (Set.Ici (0 : ℝ))
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) := fun s hs => ⟨hs, Set.mem_univ _⟩
  exact HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (f := fun s : ℝ => (s, t)) t hQ hε
    hmaps (by simp)

/-- **Second partial (frozen first variable).**

The second partial `Q' (0, 1)` of a jointly Fréchet-differentiable `Q` at `(t, t)`
along `(Ici 0) ×ˢ univ` is the within-set derivative of the frozen-first-variable
curve `s₂ ↦ Q (t, s₂)` along `Ici 0` at `t`.  Composing `Q` with the embedding
`s₂ ↦ (t, s₂)` (within-set derivative `(0, 1)`, mapping into the product set since
`t ≥ 0`). -/
theorem evalForm_jointFDeriv_partial_snd
    (Q : ℝ × ℝ → ℝ) (t : ℝ) (ht : (0 : ℝ) ≤ t) (Q' : (ℝ × ℝ) →L[ℝ] ℝ)
    (hQ : HasFDerivWithinAt Q Q' ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt (fun s : ℝ => Q (t, s)) (Q' (0, 1)) (Set.Ici (0 : ℝ)) t := by
  have hε : HasDerivWithinAt (fun s : ℝ => (t, s)) ((0 : ℝ), (1 : ℝ))
      (Set.Ici (0 : ℝ)) t :=
    (hasDerivWithinAt_const t (Set.Ici (0 : ℝ)) t).prodMk
      (hasDerivWithinAt_id t (Set.Ici (0 : ℝ)))
  have hmaps : Set.MapsTo (fun s : ℝ => (t, s)) (Set.Ici (0 : ℝ))
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) := fun s _ => ⟨ht, Set.mem_univ _⟩
  exact HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (f := fun s : ℝ => (t, s)) t hQ hε
    hmaps (by simp)

/-- **Uniqueness of the within-set derivative on `Ici 0`.**

Two within-set derivative witnesses of the same curve along `Ici 0` at a point
`t ≥ 0` have equal values (`Ici 0` is a unique-differentiability set). -/
theorem hasDerivWithinAt_Ici_unique
    {f : ℝ → ℝ} {t a b : ℝ} (ht : (0 : ℝ) ≤ t)
    (ha : HasDerivWithinAt f a (Set.Ici (0 : ℝ)) t)
    (hb : HasDerivWithinAt f b (Set.Ici (0 : ℝ)) t) : a = b := by
  have hu : UniqueDiffWithinAt ℝ (Set.Ici (0 : ℝ)) t := uniqueDiffOn_Ici (0 : ℝ) t ht
  rw [← ha.derivWithin hu, ← hb.derivWithin hu]

/-- The **scalar two-variable evaluation map** of the pullback evaluation form:
the first variable carries the metric family `g_DT`, the second variable carries
the moving image point `Φ_fam · x` and the moving pushforwards. Its *diagonal*
`s ↦ evalFormTwoVar … (s, s)` is exactly the evaluation form curve. -/
def evalFormTwoVar
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) : ℝ × ℝ → ℝ :=
  fun p => (g_DT p.1).inner (Φ_fam p.2 x)
    (mfderiv I I (Φ_fam p.2 : M → M) x v)
    (mfderiv I I (Φ_fam p.2 : M → M) x w)

/-- The diagonal of `evalFormTwoVar` is the evaluation-form curve. -/
theorem evalFormTwoVar_diag
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => evalFormTwoVar (I := I) g_DT Φ_fam x v w (s, s))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := rfl

/-- The first-slot-frozen restriction of `evalFormTwoVar` is the metric-slot
curve (image point and pushforwards frozen at `t`, metric family varying). -/
theorem evalFormTwoVar_fst
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => evalFormTwoVar (I := I) g_DT Φ_fam x v w (s, t))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) := rfl

/-- The second-slot-frozen restriction of `evalFormTwoVar` is the
pushforward-slot curve (metric frozen at `t`, image point and pushforwards
varying along the flow). -/
theorem evalFormTwoVar_snd
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    (fun s : ℝ => evalFormTwoVar (I := I) g_DT Φ_fam x v w (t, s))
      = (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := rfl

/-- **Discharge of the chain-rule regularity hypothesis (`h_chain_eval` /
`h_total_eval`).**

Let `g_DT` be a metric family, `Φ_fam` a diffeomorphism family, and fix
`t ∈ [0, T)`, `x`, `v`, `w`.  Suppose:

* `h_metric` — the **metric slot** = first partial: the curve
  `s ↦ (g_DT s).inner (Φ_fam t x) (dΦ_t v) (dΦ_t w)` (the *whole* geometric data —
  image point and pushforwards — frozen at `t`, only the metric family varying)
  has within-set derivative `G'` along `Ici 0` at `t`.  This is exactly the
  parabolic solution's pointwise time derivative
  (`deTurck_metric_slot_hasDerivWithinAt`, value `-2 Ric(g_DT t) + 𝓛`);
* `h_push` — the **moving-geometry slot** = second partial: the curve
  `s ↦ (g_DT t).inner (Φ_fam s x) (dΦ_s v) (dΦ_s w)` (the metric frozen at
  `g_DT t`, the *whole* geometric data — image point `Φ_fam s x` *and* pushforwards
  — moving along the flow; this is the fixed-metric pull-back
  `((Φ_fam s)^*(g_DT t)).inner x v w`) has within-set derivative `L'` along
  `Ici 0` at `t`.  Note the image point `Φ_fam s x` genuinely *moves* here; this
  is the flow's smooth-in-initial-condition content, supplied as a separable
  hypothesis by the variational track, *not* the frozen-base slot lemma;
* `h_joint` — the single-point **joint Fréchet differentiability** of the scalar
  two-variable evaluation map `evalFormTwoVar g_DT Φ_fam x v w` along
  `(Ici 0) ×ˢ univ` at `(t, t)`.  This is a strictly separable, single-point
  analytic fact (never a joint-`C^∞`-on-`ℝ × M` hypothesis).

Then the **evaluation-form curve** has within-set derivative `G' + L'`:

  `HasDerivWithinAt (s ↦ (g_DT s).inner (Φ_fam s x) (dΦ_s v) (dΦ_s w)) (G' + L')
     (Ici 0) t`.

The proof reads `Q := evalFormTwoVar`, applies the diagonal chain rule to obtain
the diagonal derivative `Q'(1,0) + Q'(0,1)`, identifies `Q'(1,0) = G'` and
`Q'(0,1) = L'` by uniqueness against `h_metric` / `h_push`, and rewrites the
diagonal into the evaluation form. -/
theorem deTurck_evalForm_chain_hasDerivWithinAt
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (ht : (0 : ℝ) ≤ t) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_metric : HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) G' (Set.Ici (0 : ℝ)) t)
    (h_push : HasDerivWithinAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w)) L' (Set.Ici (0 : ℝ)) t)
    {Q' : (ℝ × ℝ) →L[ℝ] ℝ}
    (h_joint : HasFDerivWithinAt (evalFormTwoVar (I := I) g_DT Φ_fam x v w) Q'
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w)) (G' + L') (Set.Ici (0 : ℝ)) t := by
  set Q := evalFormTwoVar (I := I) g_DT Φ_fam x v w with hQ
  have hdiag : HasDerivWithinAt (fun s : ℝ => Q (s, s)) (Q' (1, 0) + Q' (0, 1))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_diagonal_hasDerivWithinAt_of_jointFDeriv Q t Q' h_joint
  have hpart1 : HasDerivWithinAt (fun s : ℝ => Q (s, t)) (Q' (1, 0))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_jointFDeriv_partial_fst Q t Q' h_joint
  have hpart2 : HasDerivWithinAt (fun s : ℝ => Q (t, s)) (Q' (0, 1))
      (Set.Ici (0 : ℝ)) t :=
    evalForm_jointFDeriv_partial_snd Q t ht Q' h_joint
  have hmetric_eq : (fun s : ℝ => Q (s, t))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) := by
    rw [hQ]; exact evalFormTwoVar_fst (I := I) g_DT Φ_fam t x v w
  have hG : Q' (1, 0) = G' :=
    hasDerivWithinAt_Ici_unique ht (hmetric_eq ▸ hpart1) h_metric
  have hpush_eq : (fun s : ℝ => Q (t, s))
      = (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := by
    rw [hQ]; exact evalFormTwoVar_snd (I := I) g_DT Φ_fam t x v w
  have hL : Q' (0, 1) = L' :=
    hasDerivWithinAt_Ici_unique ht (hpush_eq ▸ hpart2) h_push
  rw [hG, hL] at hdiag
  have hdiag_eq : (fun s : ℝ => Q (s, s))
      = (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
          (mfderiv I I (Φ_fam s : M → M) x v)
          (mfderiv I I (Φ_fam s : M → M) x w)) := by
    rw [hQ]; exact evalFormTwoVar_diag (I := I) g_DT Φ_fam x v w
  rwa [hdiag_eq] at hdiag

/-- **Discharge of `h_total_eval` (the chain-rule regularity hypothesis) from the
genuine inputs.**

Given:

* `hDT_deriv` — the parabolic solution's pointwise time derivative (the DeTurck
  PDE), forcing the **metric-slot** value `Q'(1,0) = -2 Ric(g_DT t) + 𝓛`;
* `h_push_moving` — the genuine **moving-geometry slot** derivative: the
  fixed-metric pull-back curve
  `s ↦ (g_DT t).inner (Φ_fam s x) (dΦ_s v) (dΦ_s w)` has within-set derivative
  `-𝓛_{X_DT}(g_DT t)(Φ_fam t x)(dΦ_t v, dΦ_t w)` along `Ici 0` at `t` (the
  smooth-in-IC content, a separable hypothesis);
* `h_joint` — the single-point joint Fréchet differentiability of the scalar
  two-variable evaluation map `evalFormTwoVar g_DT Φ_fam x v w` along
  `(Ici 0) ×ˢ univ` at `(t, t)`,

the evaluation-form curve has within-set derivative

  `((-2 Ric(g_DT t)(Φ_fam t x)(dΦ_t v, dΦ_t w) + 𝓛_{X_DT}(g_DT t)(…)) + (-𝓛_{X_DT}(g_DT t)(…)))`,

exactly the `h_total_eval` hypothesis of `hamilton_deturck_pullback_solves_ricci_flow`
(equivalently the `h_chain_eval` hypothesis of
`pullback_time_derivative_chain_rule`).  The diagonal chain rule
`deTurck_evalForm_chain_hasDerivWithinAt` assembles the two partials; their values
are forced by uniqueness on `Ici 0`. -/
theorem deTurck_pullback_h_total_eval
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ y : M, ∀ a b : TangentSpace I y,
      HasDerivWithinAt (fun u : ℝ => (g_DT u).inner y a b)
        (deTurckRicciRHS (I := I) g_bg (g_DT s) y a b) (Set.Ici 0) s)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) (v w : TangentSpace I x)
    (h_push_moving : HasDerivWithinAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (- lieDerivMetric (I := I) (g_DT t)
          (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t)
    {Q' : (ℝ × ℝ) →L[ℝ] ℝ}
    (h_joint : HasFDerivWithinAt (evalFormTwoVar (I := I) g_DT Φ_fam x v w) Q'
      ((Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set ℝ)) (t, t)) :
    HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (((-2 : ℝ) * ricciTensor (I := I) (g_DT t) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)
          + lieDerivMetric (I := I) (g_DT t)
              (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)
              (mfderiv I I (Φ_fam t : M → M) x w))
        + (- lieDerivMetric (I := I) (g_DT t)
              (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
              (mfderiv I I (Φ_fam t : M → M) x v)
              (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t := by
  have h_metric := DifferentialGeometry.PDE.RicciFlow.deTurck_metric_slot_hasDerivWithinAt
    (I := I) g_bg g_DT T hDT_deriv Φ_fam t ht x v w
  exact deTurck_evalForm_chain_hasDerivWithinAt (I := I) g_DT Φ_fam t ht.1 x v w _ _
    h_metric h_push_moving h_joint

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
