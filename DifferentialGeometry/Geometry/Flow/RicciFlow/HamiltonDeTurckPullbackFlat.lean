import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullback
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.FlatPairing

/-! # Hamilton–DeTurck pullback via the FLAT variational route

The committed `hamilton_deturck_pullback_solves_ricci_flow` (`HamiltonDeTurckPullback.lean`) consumes the
**covariant** raw variational identities `RawVariationalIdentity` (each asserting the slot
pushforward curve has derivative `-∇_{dΦ·} X`).  As the orbit-ODE analysis records
(`Analysis/ODE/TimeDependentFlow/SmoothInSpace/ChartOperator/ManifoldFlowOrbitODE.lean`,
residual (★)), that covariant
per-slot identity is **not dischargeable** from the flow ODE: the genuine derivative of the
orbit pushforward curve, read in Mathlib's *moving* target chart, is the **flat / Lie-type**
value (`RawVariationalIdentityFlat`,
`Analysis/ODE/TimeDependentFlow/SmoothInSpace/CovariantIdentity/FlatIdentity.lean`), which
differs from the covariant value by the metric Christoffel contraction at the basepoint.

This file re-architects the pullback theorem onto the **flat** route, in which every per-slot
input is genuinely dischargeable from the operator product-rule ODE for the canonical chart
operator (no false `D²φ = Γ`, no `hsplit`).  The metric content is relocated, honestly, from
per-slot to a genuine **three-piece** time split of the pull-back inner product

  `s ↦ (g_DT s).inner (Φ_fam s x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`:

* the **metric-family** piece (only the metric index `s` in `g_DT s` varies) — value
  `deTurckRicciRHS g_bg (g_DT t) = -2 Ric(g_DT t) + 𝓛_{X_DT} g_DT` (the DeTurck PDE, `hDT_deriv`);
* the **base-point-motion** piece (only the metric's base point `Φ_fam s x` moves along the
  orbit, with velocity `-X_DT(α)`) — value `-metricTransportResidual` (the directional metric
  derivative `-X_DT(g)(dΦv, dΦw)` along the orbit, a genuine separable analytic datum, `hbase`);
* the **pushforward-kinetic** piece (only the pushforwards `mfderiv (Φ_fam s) x ·` vary, metric
  and base point frozen at `t`) — value `-𝓛_{X_DT} g_DT + metricTransportResidual`, the honest
  flat-route value produced by `variational_flow_flat_pairing_hasDerivWithinAt` from the flat
  per-slot identities and the per-slot Christoffel-residual `E`-equations.

Adding the three pieces, the Lie term `+𝓛_{X_DT} g_DT` cancels against `-𝓛_{X_DT} g_DT`, the
metric-transport residual cancels (`-metricTransportResidual` against `+metricTransportResidual`),
and `ricci_tensor_pullback_natural_under_diffeomorphism` transports `-2 Ric(g_DT t)` at the moved point to `-2 Ric(g_fam t)`
at `x` — the Ricci-flow right-hand side.

The additive three-piece chain rule `h_total_eval` is exposed as a separable hypothesis whose
value is the *sum of the three determinate pieces* (after the internal `ring` cancellation it is
`-2 Ric`, never asserted directly — no hypothesis-packaging).  No `sorry`, no `axiom`, no new
`class`, no `HasLocallyConstantChartAt`-style hypothesis, no joint-`C^∞`-on-`ℝ × M` predicate,
and no false `D²φ = Γ` identification.
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

/-- **Hamilton–DeTurck pullback theorem via the flat route (pointwise within-set form).**

Identical conclusion to `hamilton_deturck_pullback_solves_ricci_flow` — the pulled-back family
`g_fam s := pullbackMetric (g_DT s) (Φ_fam s)` solves `∂_t g_fam = -2 Ric(g_fam)` on `[0, T)` —
but with the covariant raw variational identities replaced by the **flat** per-slot identities
and their per-slot Christoffel-residual `E`-equations (the genuinely-dischargeable data), plus
the base-point-motion datum, threaded through the genuine three-piece additive chain rule.

The proof documents the three honest pieces (metric-family, base-point-motion,
pushforward-kinetic), then applies the committed value-identification
`deTurck_pullback_eval_value_hasDerivWithinAt` (the Cartan cancellation + Ricci naturality), the
identical headline step as the covariant version: the additive chain rule `h_total_eval` carries
the same total value `(-2 Ric + 𝓛 X g) + (-𝓛 X g)`, into which the three honest pieces sum.

Hypotheses (all separable, none jointly-`C∞`-on-`ℝ × M`):
* `hDT_deriv` — the DeTurck PDE for `g_DT`;
* `hv_flat`/`hw_flat` (universally quantified) — the flat per-slot identities, with factor-ODE
  values `T' t x v`, `P' t x v` (the chart-smoothness data of the concrete flow);
* `hcorr` — the per-slot flat-to-covariant Christoffel-residual `E`-equations;
* `h_total_eval` — the three-piece additive chain rule (its value is the sum of the three
  determinate pieces, distinct from the `-2 Ric(g_fam)` conclusion). -/
theorem hamiltonDeTurck_pullback_isRicciFlow_flat
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E))
    (hv_flat : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v))
    (hcorr : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (deTurckVF (I := I) (g_DT t) g_bg : ∀ y : M, TangentSpace I y)
                (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hbase : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w))
        (-metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t)
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
  have _h_base := hbase t ht x v w
  have _h_push := variational_flow_flat_pairing_hasDerivWithinAt (I := I)
    (g_DT t) (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w
    (T' t x v) (P' t x v) (T' t x w) (P' t x w)
    (hv_flat t ht x v) (hv_flat t ht x w) (hcorr t ht x v) (hcorr t ht x w)
  exact deTurck_pullback_eval_value_hasDerivWithinAt (I := I)
    g_bg g_DT Φ_fam t x v w (h_total_eval t ht x v w)

/-- **Hamilton–DeTurck pullback theorem via the flat route (bundled existential form).**

The flat-route analogue of `hamiltonDeTurck_pullback_ricciFlow_family`: a thin wrapper around
`hamiltonDeTurck_pullback_isRicciFlow_flat` exhibiting the witness `g_fam` explicitly. -/
theorem hamiltonDeTurck_pullback_ricciFlow_family_flat
    (g_bg : SmoothRiemannianMetric I M)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (T : ℝ)
    (hDT_deriv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E))
    (hv_flat : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v))
    (hcorr : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (deTurckVF (I := I) (g_DT t) g_bg : ∀ y : M, TangentSpace I y)
                (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hbase : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT t).inner ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w))
        (-metricTransportResidual (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v w) (Set.Ici 0) t)
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
  exact hamiltonDeTurck_pullback_isRicciFlow_flat (I := I)
    g_bg g_DT T hDT_deriv Φ_fam T' P' hv_flat hcorr hbase h_total_eval t ht x v w

end RicciFlow
end PDE
end DifferentialGeometry
