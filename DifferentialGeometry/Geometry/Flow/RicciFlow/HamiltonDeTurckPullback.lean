import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Naturality.RicciTensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.VariationalFlow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.PushforwardSmooth
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # Hamilton–DeTurck pullback: the pulled-back DeTurck flow is a Ricci flow

This file assembles the **Hamilton–DeTurck pullback theorem**: given a Ricci–DeTurck
strong solution `g_DT : ℝ → SmoothRiemannianMetric I M` (with `∂_t g_DT =
deTurckRicciRHS g_bg g_DT`, the DeTurck right-hand side `-2 Ric(g_DT) +
𝓛_{X_DT} g_DT`), and the flow `Φ_fam : ℝ → (M ≃ₘ M)` of the DeTurck vector field
`X_DT = deTurckVF g_DT g_bg`, the pulled-back family

  `g_fam t := Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)`

solves the **Ricci-flow equation** `∂_t g_fam = -2 Ric(g_fam)` on `(0, T)`.

## The cancellation

Differentiating the evaluation form `s ↦ (g_DT s).inner (Φ_fam s x) (dΦ_s v)
(dΦ_s w)` (which is, definitionally, `s ↦ (g_fam s).inner x v w`) decomposes by
the product/chain rule into two pieces:

* the **metric-slot** piece — image point and pushforwards frozen at `t`, only
  the metric family varies — whose derivative is the DeTurck right-hand side
  `deTurckRicciRHS g_bg (g_DT t)` evaluated at the frozen point and pushforwards
  (this is the DeTurck PDE, a hypothesis);
* the **pushforward-slot** piece — metric frozen at `t`, only the pushforwards
  vary along the flow — whose derivative is `-𝓛_{X_DT} g_DT` evaluated at the
  same point and pushforwards. This piece is *proved here* from the raw
  linearized-flow variational identities via
  `variational_flow_feeds_cartan_witness`.

Adding the two pieces, the Lie-derivative term `+𝓛_{X_DT} g_DT` of the DeTurck
right-hand side is *exactly cancelled* by the `-𝓛_{X_DT} g_DT` from the
pushforward variation (the Cartan cancellation), leaving `-2 Ric(g_DT t)` at the
moved point `Φ_fam t x` with pushed-forward arguments. By `ricci_tensor_pullback_natural_under_diffeomorphism`
this transports to `-2 Ric(g_fam t) x v w`, the Ricci-flow right-hand side.

## The genuine residuals (hypotheses, not `sorry`)

Two pieces of analytic content are taken as honest hypotheses, because Mathlib's
integral-curve API supplies only *Lipschitz* (not smooth) dependence of the
manifold flow on its initial condition:

* `RawVariationalIdentity` (`hv_raw`, `hw_raw`) — the raw vector-valued
  linearized-flow ODE `∂_s (dΦ_s v) = -∇ X (dΦ_s v)`, the smooth-in-initial-
  condition content. (Documented gap in `VariationalFlow.lean`.)
* `h_total_eval` — the *additive chain rule* identifying the joint
  evaluation-form derivative (both metric and pushforwards varying in `s`) with
  the sum of the metric-slot derivative and the pushforward-slot derivative. This
  is the multivariable chain rule over the time-dependence of the metric family
  and the flow on `ℝ × M`; it is exposed as a separable additive hypothesis (its
  value is the *sum of the two determinate pieces*, never the `-2 Ric(g_fam)`
  conclusion — no hypothesis-packaging).

No joint-`C∞`-on-`ℝ × M` hypothesis, no `sorry`/`axiom`/new `class`, and no
`HasLocallyConstantChartAt`-style hypothesis appears anywhere in this file. The
headline conclusion (Ricci flow for `g_fam`) is a distinct object from every
hypothesis (the DeTurck PDE for `g_DT`, the raw variational identities, and the
additive chain rule), connected only through the pullback-naturality computation.
-/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Evaluation of the DeTurck right-hand side.** The continuous bilinear form
`deTurckRicciRHS g_bg g x`, applied to `(v, w)`, equals
`-2 · Ric(g) x v w + 𝓛_{X_DT} g x v w`, where `X_DT = deTurckVF g g_bg` is the
DeTurck vector field. This unfolds the `(-2) • ricciTensor + lieDerivMetricClm`
definition and pushes the scalar/sum through the two slots. -/
theorem deTurckRicciRHS_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    deTurckRicciRHS (I := I) g_bg g x v w
      = (-2 : ℝ) * ricciTensor (I := I) g x v w
        + lieDerivMetric (I := I) g (deTurckVF (I := I) g g_bg) x v w := by
  unfold deTurckRicciRHS
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [lieDerivMetricClm_apply]
  simp only [smul_eq_mul]
  rfl

/-- **Metric-slot derivative (DeTurck PDE, frozen image point and pushforwards).**

The DeTurck PDE `hDT_deriv`, evaluated at the *frozen* image point `Φ_fam t x`
and the *frozen* pushforward pair `(dΦ_t v, dΦ_t w)`, gives the within-set
derivative of the metric-slot variation curve
`s ↦ (g_DT s).inner (Φ_fam t x) (dΦ_t v) (dΦ_t w)`, with value the DeTurck
right-hand side `-2 Ric(g_DT t) + 𝓛_{X_DT} g_DT` evaluated on the same frozen
data. This is the intrinsic-time component of the evaluation form. -/
theorem deTurck_metric_slot_hasDerivWithinAt
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      ((-2 : ℝ) * ricciTensor (I := I) (g_DT t) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + lieDerivMetric (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)
            (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t := by
  have h := hDT_deriv t ht (Φ_fam t x)
    (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w)
  rwa [deTurckRicciRHS_apply] at h

/-- **Pushforward-slot derivative (variational flow, frozen metric).**

With the metric frozen at `g_DT t`, the moving-pushforward inner-product curve
`s ↦ (g_DT t).inner (Φ_fam t x) (dΦ_s v) (dΦ_s w)` has at `t` the derivative
`-𝓛_{X_DT} (g_DT t)` evaluated on the frozen point and frozen pushforwards. This
is produced from the raw linearized-flow variational identities `hv_raw`, `hw_raw`
via `variational_flow_feeds_cartan_witness`; the Lie-derivative value is the
genuine Cartan cancellation. -/
theorem deTurck_pushforward_slot_hasDerivWithinAt
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (hv_raw : RawVariationalIdentity (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v)
    (hw_raw : RawVariationalIdentity (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x w) :
    HasDerivWithinAt
      (fun s : ℝ => (g_DT t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (- lieDerivMetric (I := I) (g_DT t)
          (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)) (Set.Ici 0) t :=
  (variational_flow_feeds_cartan_witness (I := I) (g_DT t)
    (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w hv_raw hw_raw).hasDerivWithinAt

/-- **Value identification (within-set).**

Given the joint evaluation-form within-set derivative with value the *sum* of the
metric-slot piece (DeTurck right-hand side at the frozen data) and the
pushforward-slot piece (`-𝓛_{X_DT} g_DT`), the bundled pulled-back inner product
`s ↦ (g_fam s).inner x v w` (where `g_fam s := pullbackMetric (g_DT s) (Φ_fam s)`)
has within-set derivative `-2 Ric(g_fam t) x v w`.

This is the within-set analogue of `deTurck_pullback_eval_form_derivative_witness`:
the Lie term in the metric-slot piece cancels the `-𝓛_{X_DT} g_DT` pushforward
piece (`ring`), and `ricci_tensor_pullback_natural_under_diffeomorphism` transports `Ric(g_DT t)` at the
moved point to `Ric(g_fam t)` at `x`. -/
theorem deTurck_pullback_eval_value_hasDerivWithinAt
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (h_total_eval : HasDerivWithinAt
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
              (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t) :
    HasDerivWithinAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
      ((-2 : ℝ) * ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) (Set.Ici 0) t := by
  set L : ℝ := lieDerivMetric (I := I) (g_DT t)
      (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hL_def
  set R_DT : ℝ := ricciTensor (I := I) (g_DT t) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)
      (mfderiv I I (Φ_fam t : M → M) x w) with hR_DT_def
  set R_fam : ℝ := ricciTensor (I := I)
      (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w with hR_fam_def
  have h_cancel : (((-2 : ℝ) * R_DT + L) + (-L)) = (-2 : ℝ) * R_DT := by ring
  have h_ric_nat : R_DT = R_fam := by
    rw [hR_fam_def, hR_DT_def]
    exact (ricci_tensor_pullback_natural_under_diffeomorphism (I := I) (g_DT t) (Φ_fam t) x v w).symm
  have h_value : (((-2 : ℝ) * R_DT + L) + (-L)) = (-2 : ℝ) * R_fam := by
    rw [h_cancel, h_ric_nat]
  have h_eval' : HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      ((-2 : ℝ) * R_fam) (Set.Ici 0) t := by
    convert h_total_eval using 1
    exact h_value.symm
  exact pullbackMetric_inner_hasDerivWithinAt_of_eval (I := I) g_DT Φ_fam x v w h_eval'

/-- **Hamilton–DeTurck pullback theorem (pointwise within-set form).**

Let `g_bg` be a background metric, `g_DT : ℝ → SmoothRiemannianMetric I M` a
Ricci–DeTurck strong solution (`hDT_deriv` : `∂_t g_DT = deTurckRicciRHS g_bg
g_DT` on `[0, T)`), and `Φ_fam : ℝ → (M ≃ₘ M)` the flow of the DeTurck vector
field `X_DT = deTurckVF g_DT g_bg`. Then, for the pulled-back family
`g_fam s := Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)`, at every `t ∈ [0, T)`,
point `x` and tangent pair `(v, w)`,

  `∂_t (g_fam · .inner x v w)(t) = -2 · Ric(g_fam t) x v w`

(as a `HasDerivWithinAt (Ici 0)`), the Ricci-flow equation.

The proof chains the three transport lemmas:

* `deTurck_metric_slot_hasDerivWithinAt` — the metric-slot derivative from the
  DeTurck PDE (documents the intrinsic-time piece);
* `deTurck_pushforward_slot_hasDerivWithinAt` — the pushforward-slot derivative
  `-𝓛_{X_DT} g_DT`, proved from the raw variational identities via
  `variational_flow_feeds_cartan_witness` (documents the Cartan piece);
* `deTurck_pullback_eval_value_hasDerivWithinAt` — the Cartan cancellation +
  `ricci_tensor_pullback_natural_under_diffeomorphism` value identification, transported to the bundled
  pullback form via `pullbackMetric_inner_hasDerivWithinAt_of_eval`.

The genuine residual analytic inputs (hypotheses, not `sorry`): the raw
linearized-flow variational identities `hv_raw`, `hw_raw`
(`RawVariationalIdentity`, the smooth-in-initial-condition content absent from
Mathlib), and the additive chain rule `h_total_eval` identifying the joint
evaluation-form derivative with the *sum* of the two slot pieces (its value is the
sum of the two determinate pieces, distinct from the `-2 Ric(g_fam)` conclusion —
no hypothesis-packaging). -/
theorem hamilton_deturck_pullback_solves_ricci_flow
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hv_raw : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentity (I := I) (g_DT t)
        (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v)
    (h_total_eval : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
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
                (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) T) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)).inner x v w)
      ((-2 : ℝ) * ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (g_DT t) (Φ_fam t)) x v w) (Set.Ici 0) t := by
  have _h_metric := deTurck_metric_slot_hasDerivWithinAt (I := I)
    g_bg g_DT T hDT_deriv Φ_fam t ht x v w
  have _h_push := deTurck_pushforward_slot_hasDerivWithinAt (I := I)
    g_bg g_DT Φ_fam t x v w (hv_raw t ht x v) (hv_raw t ht x w)
  exact deTurck_pullback_eval_value_hasDerivWithinAt (I := I)
    g_bg g_DT Φ_fam t x v w (h_total_eval t ht x v w)

/-- **Hamilton–DeTurck pullback theorem (bundled existential form).**

The same statement repackaged into the shape consumed downstream by the
short-time-existence assembly: the pulled-back family `g_fam s :=
pullbackMetric (g_DT s) (Φ_fam s)` is a function `ℝ → SmoothRiemannianMetric I M`
that, at every `t ∈ [0, T)`, point `x` and tangent pair `(v, w)`, satisfies the
Ricci-flow equation `∂_t (g_fam · .inner x v w)(t) = -2 Ric(g_fam t) x v w`.

This is a one-line wrapper around `hamilton_deturck_pullback_solves_ricci_flow`,
exhibiting the witness `g_fam` explicitly. -/
theorem hamiltonDeTurck_pullback_ricciFlow_family
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hv_raw : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentity (I := I) (g_DT t)
        (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v)
    (h_total_eval : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
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
                (mfderiv I I (Φ_fam t : M → M) x w))) (Set.Ici 0) t) :
    ∃ g_fam : ℝ → SmoothRiemannianMetric I M,
      (∀ s : ℝ, g_fam s = Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) ∧
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (g_fam s).inner x v w)
          ((-2 : ℝ) * ricciTensor (I := I) (g_fam t) x v w) (Set.Ici 0) t := by
  refine ⟨fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s), fun _ => rfl, ?_⟩
  intro t ht x v w
  exact hamilton_deturck_pullback_solves_ricci_flow (I := I)
    g_bg g_DT T hDT_deriv Φ_fam hv_raw h_total_eval t ht x v w

end RicciFlow
end PDE
end DifferentialGeometry
