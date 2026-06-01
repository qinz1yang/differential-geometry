import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanFormula
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.RicciFlow.Pullback.PushforwardVF
import DifferentialGeometry.Integral.Connection.LeviCivita
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Cartan-Lie cancellation propositional identity for the DeTurck pullback

For a smooth Riemannian metric `g` on a smooth manifold `M`, a smooth tangent
vector field `X` (the DeTurck vector field of an underlying metric pair), a
diffeomorphism `Φ : M ≃ₘ⟮I, I⟯ M`, a base point `x : M` and tangent vectors
`v, w : T_x M`, the time derivative

  `Lpush := d/ds [ g.inner (Φ_s x) (dΦ_s v) (dΦ_s w) ] |_{s = t}`

of the moving-pushforward inner-product variation along a smooth flow `Φ_fam`
satisfying `∂_s Φ_fam = -X ∘ Φ_fam` admits the substantive identification

  `Lpush = - lieDerivMetric g X (Φ x) (mfderiv Φ x v) (mfderiv Φ x w)`,

i.e. the symmetrised covariant derivative of `X` against `g`, evaluated on the
pushforward pair, with a minus sign coming from the flow generator `-X`.

This file packages the propositional Cartan-Lie cancellation step in two
layers:

* the **value-level** primitive
  `lie_deriv_metric_neg_eq_pushforward_variation_sum` carries the substantive
  algebra: given the per-slot variation values `A'` (first slot)
  and `B'` (second slot), each propositionally identified with
  `-g.inner y (∇^g_{dΦv_i} X) dΦw_j`, the negated Cartan formula tells us
  `A' + B' = -lieDerivMetric g X y (dΦv) (dΦw)`. The substantive content is
  `cartan_formula_for_lie_deriv_metric` invoked once and reorganised algebraically;

* the **derivative-level** primitive
  `cartan_cancellation_derivative_witness` packages the same identity with
  `HasDerivAt` inputs on the per-slot variation curves and assembles the total
  pushforward-variation derivative value, identifying it with the negated Lie
  derivative.

The per-slot variation values (`A'` and `B'`) carry the genuine flow content:
each is identified with `-g.inner y (∇^g_{dΦv_i} X) dΦw_j` by the variational
chain rule applied to the moving pushforward `s ↦ mfderiv (Φ_fam s) x v` (which
takes value `-∇^g_{dΦv} X` at `s = t` by `∂_s Φ_fam = -X ∘ Φ_fam` and the
manifold-derivative variational identity for time-dependent flows). The
derivative-of-pushforward content is the prerequisite that requires
smooth-in-IC variational ODE data and is exposed here as the per-slot value
hypotheses `h_A_value` and `h_B_value`. The present file's job is purely the
algebraic Cartan-cancellation packaging on top of those per-slot identifications.

When this primitive is consumed inside `EvaluationFormWitness`, the per-slot
value hypotheses are supplied from the variational ODE step (proved separately
in the smooth-in-IC track), and the headline conclusion
`Lpush = -lieDerivMetric ...` of `h_cartan_cancellation` falls out by feeding
the per-slot values into this primitive's sum-and-Cartan step. -/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace Pullback

open Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Negative Cartan formula for the metric Lie derivative.**

The negated bilinear form `-(𝓛_X g)(p, q)` decomposes as the sum of the two
negated symmetrised covariant-derivative pieces. This is the substantive
algebraic identity (Cartan formula + negation) used to convert per-slot
variations into the negative Lie derivative. -/
theorem neg_lieDerivMetric_eq_neg_killing_sum
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y) :
    -lieDerivMetric (I := I) g X y p q =
      (-g.inner y ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y p) q)
      + (-g.inner y p ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y q)) := by
  rw [cartan_formula_for_lie_deriv_metric (I := I) g X y p q]
  ring

/-- **Value-level Cartan-cancellation primitive.**

Given two real values `A'` and `B'` and per-slot value identities

  `A' = -g.inner y (∇^g_p X) q`     (first-slot variation)
  `B' = -g.inner y p (∇^g_q X)`     (second-slot variation)

conclude `A' + B' = -lieDerivMetric g X y p q`. The proof is the Cartan
formula on the right-hand side, combined with the two value identities.

This is the substantive algebraic identity that drives the Cartan-Lie
cancellation in the DeTurck pullback chain. The two value identities encode
the variational chain-rule output for the moving pushforwards (each takes
value `-∇^g_{dΦ v_i} X` at the cancellation time, since the flow generator is
`-X`). -/
theorem lie_deriv_metric_neg_eq_pushforward_variation_sum
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y)
    (A' B' : ℝ)
    (h_A_value : A' = -g.inner y ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y p) q)
    (h_B_value : B' = -g.inner y p ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y q)) :
    A' + B' = -lieDerivMetric (I := I) g X y p q := by
  rw [h_A_value, h_B_value]
  rw [neg_lieDerivMetric_eq_neg_killing_sum (I := I) g X y p q]

/-- **Sum-cancellation form.** Given `A' + B' = -lieDerivMetric g X y p q`
and a total value `Lpush = A' + B'`, conclude `Lpush = -lieDerivMetric g X y p q`.
A pure transitivity packaging — the substantive content sits in the per-slot
identities that the consumer feeds into
`lie_deriv_metric_neg_eq_pushforward_variation_sum`. -/
theorem lpush_eq_neg_lieDerivMetric_of_sum
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y)
    (A' B' Lpush : ℝ)
    (h_sum : Lpush = A' + B')
    (h_AB : A' + B' = -lieDerivMetric (I := I) g X y p q) :
    Lpush = -lieDerivMetric (I := I) g X y p q := by
  rw [h_sum, h_AB]

/-- **Combined value-level form** — the substantive Cartan-cancellation
identity bundled with the sum-cancellation step.

Given two per-slot variation values `A'` and `B'`, their pointwise
identification with the two negated Killing-pieces, and a value `Lpush`
identified with `A' + B'`, conclude
`Lpush = -lieDerivMetric g X y p q`.

This is the propositional form of the Cartan-Lie cancellation identity required
by `EvaluationFormWitness.h_cartan_cancellation` — modulo the per-slot value
identities, which encode the variational ODE content of the moving
pushforwards. -/
theorem cartan_cancellation_value_identity
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (y : M) (p q : TangentSpace I y)
    (A' B' Lpush : ℝ)
    (h_A_value : A' = -g.inner y ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y p) q)
    (h_B_value : B' = -g.inner y p ((LeviCivita (I := I) g)
        (X : ∀ x : M, TangentSpace I x) y q))
    (h_sum : Lpush = A' + B') :
    Lpush = -lieDerivMetric (I := I) g X y p q :=
  lpush_eq_neg_lieDerivMetric_of_sum (I := I) g X y p q A' B' Lpush h_sum
    (lie_deriv_metric_neg_eq_pushforward_variation_sum (I := I) g X y p q
      A' B' h_A_value h_B_value)

/-- **Derivative-level Cartan-cancellation witness.**

Given a smooth metric `g`, a smooth vector field `X`, a smooth flow
`Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`, a fixed time `t`, base point `x`, and a
tangent pair `(v, w)`:

* `h_A` — the first-slot pushforward variation curve
  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam t) x w)`
  has derivative `A'` at `t`;

* `h_A_value` — the value identity `A' = -g.inner y (∇^g_{dΦv} X) dΦw`
  (the variational chain-rule output for slot 1, identifying the time
  derivative of the moving pushforward in slot 1 with the negative covariant
  derivative of `X` along the slot-1 pushforward — the genuine flow content);

* `h_B` and `h_B_value` — the slot-2 analogue;

* `h_total` — the combined two-slot pushforward variation curve
  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`
  has derivative `Lpush` at `t`;

* `h_sum` — the additive assembly identity `Lpush = A' + B'`.

Then the same total curve has derivative
`-lieDerivMetric g X (Φ_fam t x) (dΦ v) (dΦ w)` at `t`, with the substantive
value identification `Lpush = -lieDerivMetric ...` derived from the
Cartan-cancellation packaging.

This is the derivative-level form of the Cartan-Lie cancellation identity. -/
theorem cartan_cancellation_derivative_witness
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M)
    (v w : TangentSpace I x)
    (Lpush A' B' : ℝ)
    (h_A : HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      A' t)
    (h_B : HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      B' t)
    (h_A_value : A' = -g.inner (Φ_fam t x)
      ((LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v))
      (mfderiv I I (Φ_fam t : M → M) x w))
    (h_B_value : B' = -g.inner (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      ((LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x w)))
    (h_total : HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      Lpush t)
    (h_sum : Lpush = A' + B') :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) t := by
  let _ := h_A; let _ := h_B
  have hL : Lpush = -lieDerivMetric (I := I) g X (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) :=
    cartan_cancellation_value_identity (I := I) g X (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w)
      A' B' Lpush h_A_value h_B_value h_sum
  convert h_total using 1
  exact hL.symm

/-- **Cartan-Lie cancellation identity** in the exact shape required by
`EvaluationFormWitness.h_cartan_cancellation`.

For a smooth metric family `g_DT : ℝ → SmoothRiemannianMetric I M`, a
background metric `g_bg`, a smooth flow `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`, a fixed
time `t`, base point `x`, and tangent pair `(v, w)`, given:

* the per-slot pushforward-variation values `A'` (first slot) and `B'`
  (second slot) for the inner product against `g_DT t` evaluated at the
  fixed image point `Φ_fam t x`;
* per-slot value identifications stating that each variation value equals the
  negative covariant derivative of `deTurckVF (g_DT t) g_bg` along the
  corresponding fixed pushforward (the variational chain-rule output for the
  flow `∂_s Φ_fam = -deTurckVF ∘ Φ_fam`);
* a value `Lpush` identified with `A' + B'` (the additive assembly of the
  per-slot pieces);

conclude that

  `Lpush = -lieDerivMetric (g_DT t) (deTurckVF (g_DT t) g_bg) (Φ_fam t x)
        (mfderiv (Φ_fam t) x v) (mfderiv (Φ_fam t) x w)`,

i.e. the substantive identity required by
`EvaluationFormWitness.h_cartan_cancellation`. -/
theorem deTurck_pullback_cartan_cancellation
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (g_bg : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M)
    (v w : TangentSpace I x)
    (A' B' Lpush : ℝ)
    (h_A_value : A' = -(g_DT t).inner (Φ_fam t x)
      ((LeviCivita (I := I) (g_DT t))
        (deTurckVF (I := I) (g_DT t) g_bg :
            ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v))
      (mfderiv I I (Φ_fam t : M → M) x w))
    (h_B_value : B' = -(g_DT t).inner (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      ((LeviCivita (I := I) (g_DT t))
        (deTurckVF (I := I) (g_DT t) g_bg :
            ∀ x : M, TangentSpace I x) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x w)))
    (h_sum : Lpush = A' + B') :
    Lpush = -lieDerivMetric (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) :=
  cartan_cancellation_value_identity (I := I) (g_DT t)
    (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
    (mfderiv I I (Φ_fam t : M → M) x v)
    (mfderiv I I (Φ_fam t : M → M) x w)
    A' B' Lpush h_A_value h_B_value h_sum

end Pullback
end RicciFlow
end PDE
end DifferentialGeometry
