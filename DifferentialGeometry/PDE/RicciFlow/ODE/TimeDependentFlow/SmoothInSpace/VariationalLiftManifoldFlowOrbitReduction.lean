import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftManifoldFlowClose

/-!
# The canonical chart operator of the orbit flow IS the pushforward

The canonical chart-coordinate operator `chartCloseDop Φ_fam α x s`
(`SmoothInSpace/VariationalLiftManifoldFlowClose.lean`) is the moving inverse target
trivialisation `trivFromE α (Φ_fam s x)` post-composed with the chart-coordinate spatial
Fréchet derivative `mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ Φ_fam s) x`, both read through the
*fixed* chart at `α := Φ_fam t x`.

This file establishes the **value-level reduction** of the canonical chart operator to the
genuine manifold pushforward: applied to a source vector `v`, and at any time `s` for which
the orbit point `Φ_fam s x` lies in the fixed chart source of `α`,

  `chartCloseDop Φ_fam α x s v = mfderiv I I (Φ_fam s) x v`           (in `TangentSpace I (Φ_fam s x) = E`).

The proof is the *raw-value chart dictionary* `mfderiv_flow_eq_chartFderiv_apply`
(`SmoothInSpace/VariationalLiftChartDictionary.lean`) read **backwards**: that lemma states

  `mfderiv I I F x v = trivFromE α (F x) (mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ F) x v)`,

for `F = Φ_fam s`, and the right-hand side is *definitionally* `chartCloseDop Φ_fam α x s v`
(via `chartCloseDop_apply`).  In words: the moving inverse target trivialisation undoes the
moving target trivialisation built into the chart-coordinate derivative, so the composite is
exactly the diffeomorphism pushforward read in the fibre `TangentSpace I (Φ_fam s x)`.

## Why this is the genuine bridge to the variational identity

`RawVariationalIdentity g X Φ_fam t x v`
(`TimeDependentFlow/VariationalFlow.lean`) is by definition the statement that the orbit
pushforward curve

  `s ↦ (mfderiv I I (Φ_fam s) x v : E)`

has, at time `t`, the vector-valued derivative `-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`.

The reduction below identifies the connector's left-hand reading
`s ↦ chartCloseDop Φ_fam α x s v` with *exactly* this orbit pushforward curve on a
neighbourhood of `t` (the orbit stays in the chart source of `α` near `t`, since
`Φ_fam t x = α`).  Hence the connector's operator-valued ODE input
`hDchart : HasDerivAt (chartCloseDop Φ_fam α x) Dchart' t` is — at the value level —
the genuine variational ODE of the pushforward, with `Dchart' v = d/ds (mfderiv (Φ_fam s) x v)|_t`.
The connector's value-level input `hsplit` then equates *this derivative value* with the
flat-trivialised-plus-metric-Christoffel decomposition.

## What this file proves, and the residual it leaves

* `chartCloseDop_apply_eq_mfderiv` — the per-time value reduction (an honest `E`-equation, no
  eventual quantifier);
* `chartCloseDop_basepoint_apply_eq_mfderiv` — the same at `s = t` (where `Φ_fam t x = α` is in
  its own chart source automatically), giving `chartCloseDop Φ_fam α x t v = mfderiv (Φ_fam t) x v`;
* `chartCloseDop_eventuallyEq_mfderiv_orbit` — the *eventual* (`=ᶠ[𝓝 t]`) reduction of the
  operator-applied curve `s ↦ chartCloseDop Φ_fam α x s v` to the orbit pushforward curve
  `s ↦ mfderiv (Φ_fam s) x v`, valid near `t` from the eventual chart membership of the orbit
  (`flow_orbit_eventually_mem_chartAt_source`);
* `rawVariationalIdentity_iff_hasDerivAt_chartCloseDop` — the consequence: under the eventual
  reduction, `RawVariationalIdentity` holds **iff** `s ↦ chartCloseDop Φ_fam α x s v` has the
  covariant-derivative value at `t`, i.e. the connector's `hDchart`/`hsplit` data (with
  `Dchart'` the genuine pushforward variational derivative) is *equivalent* to the variational
  identity — the honest statement that closing `hsplit` for the concrete orbit flow is closing
  the covariant variational identity itself.

This is the genuinely metric-dependent residual: the reduction here is `g`-free (pure
chart-trivialisation round-trip), but the *value* of the pushforward variational derivative —
the right-hand side of `hsplit`, the covariant `-(LeviCivita g) X (α) w` — is the Levi-Civita
covariant variational identity `D_s (dΦ_s v) = -∇_{dΦ_s v} X`, whose flat chart-coordinate
representation differs from the Lie-type derivative by the metric Christoffel symbol (entering
via metric-compatibility).  That covariant variational identity is **not** discharged here; it
is the documented metric-covariant reconciliation.

No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no
joint-`C^∞`-on-`ℝ × M` predicate.  No hypothesis-packaging: every conclusion is an `E`-equation
or an `=ᶠ`/iff statement derived from the chart dictionary, never the `HasDerivAt` target
asserted as a hypothesis.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section OrbitReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The canonical chart operator applied to `v` is the pushforward.**

For a time-`s` diffeomorphism `Φ_fam s`, and at any time `s` whose orbit point `Φ_fam s x`
lies in the fixed chart source of `α`, the canonical chart-coordinate operator applied to the
source vector `v` reproduces the manifold pushforward read in the fibre `TangentSpace I (Φ_fam s x)`:

  `chartCloseDop Φ_fam α x s v = mfderiv I I (Φ_fam s) x v`.

Genuine content: this is the raw-value chart dictionary `mfderiv_flow_eq_chartFderiv_apply`
read backwards.  `chartCloseDop_apply` rewrites the left side as
`trivFromE α (Φ_fam s x) (mfderiv (extChartAt I α ∘ Φ_fam s) x v)`, which the dictionary equates
to `mfderiv I I (Φ_fam s) x v`.  The moving inverse target trivialisation undoes the moving
target trivialisation in the chart-coordinate derivative.  No hypothesis-packaging: the
conclusion is an `E`-equation, not the variational `HasDerivAt` target. -/
theorem chartCloseDop_apply_eq_mfderiv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) (v : TangentSpace I x)
    (hsrc : (Φ_fam s : M → M) x ∈ (chartAt H α).source) :
    chartCloseDop (I := I) Φ_fam α x s v = mfderiv I I (Φ_fam s : M → M) x v := by
  have hF : MDifferentiableAt I I (Φ_fam s : M → M) x :=
    flowFamily_mdifferentiableAt_fixed_time (I := I) Φ_fam s x
  rw [chartCloseDop_apply]
  exact (mfderiv_flow_eq_chartFderiv_apply (I := I) (Φ_fam s : M → M) α v hF hsrc).symm

/-- **At the basepoint time `t`, the canonical chart operator IS the pushforward of `Φ_fam t`.**

With `α := Φ_fam t x`, the orbit point at `s = t` is `Φ_fam t x = α`, which lies in its own
chart source automatically (`mem_chart_source`).  Hence `chartCloseDop_apply_eq_mfderiv`
specialises to

  `chartCloseDop Φ_fam (Φ_fam t x) x t v = mfderiv I I (Φ_fam t) x v`.

The connector evaluates `Dchart'` (the time-derivative of `chartCloseDop`) at `t`; this lemma
fixes the *value* of `chartCloseDop` at `t` as the genuine pushforward, so the variational ODE
input is anchored at the true orbit pushforward. -/
theorem chartCloseDop_basepoint_apply_eq_mfderiv
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x) :
    chartCloseDop (I := I) Φ_fam (Φ_fam t x) x t v
      = mfderiv I I (Φ_fam t : M → M) x v :=
  chartCloseDop_apply_eq_mfderiv (I := I) Φ_fam (Φ_fam t x) x t v (mem_chart_source H _)

/-- **Eventual reduction of the operator-applied curve to the orbit pushforward curve.**

Along the orbit `s ↦ Φ_fam s x`, which is continuous at `t` with `Φ_fam t x = α` in the chart
source of `α`, the orbit point stays in the fixed chart source of `α` for all `s` near `t`
(`flow_orbit_eventually_mem_chartAt_source`).  On that neighbourhood the per-time reduction
`chartCloseDop_apply_eq_mfderiv` applies, giving the eventual equality of the two curves:

  `(s ↦ chartCloseDop Φ_fam α x s v) =ᶠ[𝓝 t] (s ↦ mfderiv I I (Φ_fam s) x v)`,

with `α := Φ_fam t x`.

This is the connector's left-hand reading identified, near `t`, with the genuine orbit
pushforward curve that `RawVariationalIdentity` differentiates.  Continuity of the orbit is a
separable input (never joint `C^∞` on `ℝ × M`). -/
theorem chartCloseDop_eventuallyEq_mfderiv_orbit
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    (fun s : ℝ => chartCloseDop (I := I) Φ_fam (Φ_fam t x) x s v)
      =ᶠ[𝓝 t] (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v) := by
  have hmem : ∀ᶠ s : ℝ in 𝓝 t,
      (Φ_fam s : M → M) x ∈ (chartAt H (Φ_fam t x)).source :=
    flow_orbit_eventually_mem_chartAt_source (I := I) Φ_fam t x hcontAt
  filter_upwards [hmem] with s hs
  exact chartCloseDop_apply_eq_mfderiv (I := I) Φ_fam (Φ_fam t x) x s v hs

/-- **`RawVariationalIdentity` is the statement that `chartCloseDop` carries the covariant value.**

Under the eventual reduction of the operator-applied curve `s ↦ chartCloseDop Φ_fam α x s v`
to the orbit pushforward curve `s ↦ mfderiv (Φ_fam s) x v` (`chartCloseDop_eventuallyEq_mfderiv_orbit`),
the manifold variational identity `RawVariationalIdentity g X Φ_fam t x v` holds **iff** the
operator-applied curve has, at `t`, the covariant-derivative value
`-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`:

  `RawVariationalIdentity g X Φ_fam t x v
     ↔ HasDerivAt (fun s => chartCloseDop Φ_fam (Φ_fam t x) x s v)
         (-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)) t`.

`RawVariationalIdentity` is by definition `HasDerivAt (s ↦ mfderiv (Φ_fam s) x v) (covariant value) t`,
so the two `HasDerivAt` statements are about eventually-equal functions and transfer by
`Filter.EventuallyEq.hasDerivAt_iff`.

This exhibits, with no metric step performed here, the exact shape the connector consumes: the
left-hand reading `chartCloseDop` carries the covariant variational value precisely when the
variational identity holds.  The remaining content — the covariant *value* of the pushforward
derivative — is the Levi-Civita covariant variational identity, the genuinely metric-dependent
residual, not discharged here. -/
theorem rawVariationalIdentity_iff_hasDerivAt_chartCloseDop
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v
      ↔ HasDerivAt (fun s : ℝ => chartCloseDop (I := I) Φ_fam (Φ_fam t x) x s v)
          (-(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v)) t := by
  unfold RawVariationalIdentity
  exact (Filter.EventuallyEq.hasDerivAt_iff
    (chartCloseDop_eventuallyEq_mfderiv_orbit (I := I) Φ_fam t x v hcontAt)).symm

end OrbitReduction

end DifferentialGeometry.PDE.RicciFlow.ODE
