# StepBLocalMetrics.lean — B-metric local metric limits (`lbl394` metric part, 2026-06-13)

## UPDATE 2026-06-21 — `hsmooth` frontier CLOSED; wrapper now rests on honest containments

The "frontier-1 smoothness gap" recorded below is **gone**. `exists_metricLimit_normalCoord`
no longer takes an `hsmooth : ContDiffOn ℝ ⊤ (normalCoordMetric …) U` hypothesis. It now
takes the honest geometric containment `hsub : ∀ k, U ⊆ ball 0 (expMapC2Radius (X.obj k).metric (c k))`
and discharges the `C^∞` smoothness internally via
`StepBInputs.contDiffOn_normalCoordMetric_of_subset_expBall`. That bridge rests on
`normalCoordMetric_contDiffOn_expBall` (StepBInputs), which is the FORWARD-only pullback
`C^∞` on the named ball — built from `expMap_contMDiffAt_infty_of_norm_lt_radius` (the
single-radius `C^∞` forward exp, which already exists in `GaussLemmaPullback`/`OffZero`).
The note below claiming "expMapDiffeo is only `C^1` so even proving the field is real work"
was correct for the inverse but NOT for the metric: the metric pullback uses only the
forward map, so it is `C^∞` unconditionally. Verified green (targeted build, no new sorry).

**Remaining metric-side frontier** (now the ONLY one): the uniform-radius wiring — a single
open `U` with `U ⊆ ball 0 (input.radius k (c k))` (hdom) AND `U ⊆ ball 0 (expMapC2Radius …)`
(hsub) for all `k`, i.e. a uniform positive lower bound on both radii across the sequence.
That is Step-A geometric input (bounded geometry + inj-radius lower bound), not analysis.

## Status: generic theorem COMPLETE; HCG `β`-wrapper deferred on two named B-input gaps

**Verification PASSED**: focused check + targeted build green (no warnings); axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) for `exists_metricLimit_on`.

## Delivered
- `exists_metricLimit_on` — generic model-coordinate local metric limit. From
  `IsOpen U`, `∀k ContDiffOn ℝ ⊤ (gLoc k) U`, derivative bounds on compacts ⊆ `U`
  (constants before `k`), and per-`k` uniform equivalence `½‖v‖² ≤ gₖ(z)(v,v) ≤ 2‖v‖²`,
  produces a subsequence `φ`, a limit `gInf`, `ContDiffOn ℝ ⊤ gInf U`,
  `MapCInfConvOnCompacts U (gLoc∘φ) gInf`, and the **retained** equivalence
  `½‖v‖² ≤ gInf(z)(v,v) ≤ 2‖v‖²` on `U` (so `gInf` is positive definite there).
  Proof: `exists_cInf_subseq_on` for the convergence; the equivalence passes to the
  pointwise limit (`tendsto_of_cInf`, evaluation continuity `fun_prop`,
  `ge_of_tendsto`/`le_of_tendsto`). Target `E →L[ℝ] E →L[ℝ] ℝ` is finite-dim
  automatically (no `InnerProductSpace E` in scope, so no slow synthesis).

## HCG `β`-indexed wrapper — deferred, with the exact missing inputs

The book sequence is `gLoc k = normalCoordMetric (X.obj k) (c k)` for a per-`k` chart
center `c k : (X.obj k).M` (same `β`, different manifolds `M_k`), on the **fixed** ball
`vec E^β`. Wiring `NormalCoordMetricBoundInput` (B-input) into `exists_metricLimit_on`
needs two facts the current input does NOT provide — neither should be faked:

1. **Smoothness.** `exists_metricLimit_on` needs `∀ k, ContDiffOn ℝ ⊤ (normalCoordMetric
   (X.obj k) (c k)) U`. `NormalCoordMetricBoundInput` has only derivative *bounds*, no
   `ContDiffOn` field. Worse, the realized `expMapDiffeo` is a `PartialDiffeomorph … 1`
   (only `C^1`), so even proving the field is real work (the metric pullback is `C^∞`
   mathematically, but the realized normal-coordinate API exposes `C^1`). **Smallest
   fix:** add a `metric_smooth : ∀ k x, ContDiffOn ℝ ⊤ (normalCoordMetric (X.obj k) x)
   (ball 0 (radius k x))` field to `NormalCoordMetricBoundInput` (honest book-external),
   OR upgrade the normal-coordinate `expMapDiffeo` API to `C^∞`.
2. **Uniform radius.** `exists_metricLimit_on`'s `U` is fixed across `k`, but the input's
   `radius k (c k)` is per-`k`. Need `∃ R > 0, ∀ k, Metric.ball 0 R ⊆ ball 0 (radius k
   (c k))`, i.e. a uniform lower bound on the radii (the book's `vec E^β` has a fixed
   radius `205 e^{20cC} λ^α`). **Smallest fix:** a `radius_lb` field or a Step-A lemma
   giving the uniform `R`.

Both are Step-A / B-input follow-ups (the planner's "full Step-A β wiring is too much"
clause). The generic engine is ready to consume them the moment they exist.

## Next
The `β`-wrapper is a thin application once (1) and (2) land. B-trans (`StepBTransition`)
has the same `C^1`-vs-`C^∞` smoothness dependency for `normalTransition`.

## HCG wrapper DELIVERED by honest exposure (2026-06-13, frontier-1 push)

`exists_metricLimit_normalCoord` (new `section HCGNormalCoord`) wires
`NormalCoordMetricBoundInput` + `c : ∀ k, (X.obj k).M` into `exists_metricLimit_on`.
**Verification PASSED** (focused check + targeted build green; axiom-clean
`[propext, Classical.choice, Quot.sound]`). Fixed-`β` only (one center sequence), NOT
the finite diagonal over all `β`.

The two frontier-1 facts are **honestly exposed as explicit hypotheses** (bare
statements, not renamed predicates), per the planner's "proving OR honestly exposing"
clause:
- `hsmooth : ∀ k, ContDiffOn ℝ ⊤ (normalCoordMetric (X.obj k) (c k)) U` — the genuine
  smoothness; blocked on the foundational gap below.
- `hdom : ∀ k, U ⊆ ball 0 (input.radius k (c k))` — uniform domain containment.

The bound side uses `input.metric_deriv` (with `M = input.metricC r`) and `metric_equiv`
directly; the slow nested-CLM synthesis under `InnerProductSpace E` needs
`set_option synthInstance.maxHeartbeats 800000` (scoped). The wrapper is a thin, honest
application — the moment a `ContDiffOn ⊤` producer for `normalCoordMetric` lands, B-metric
completes for a fixed `β`.

### Frontier-1 root gap — corrected after ODE-layer audit (2026-06-13)

The `n`-dependent radius in the old finite-order route is real:

```
exp ContMDiffAt ⊤  ⟸  chart-flow Φ ContDiffOn ⊤ on a fixed ball
   (expMap_contMDiffAtN_of_norm_lt → contMDiffAt_infty)
chart-flow Φ ContDiffOn ⊤  ⟸  exists_chartPhase_…_combined_nat  [only the _nat form exists]
combined_nat radius  ⟸  exists_contDiffOn_flow_Cnat = flowCkPred_all n  [domain is n-DEPENDENT]
```

`exists_contDiffOn_flow_Cnat` (`VariationalMapContDiffOnK.lean`) is `flowCkPred_all n`, a
strong induction (`flowCkPred_base`=C¹ Picard–Lindelöf; `flowCkPred_step` via the augmented
flow `augVF`). `FlowCkPred n` returns an **existential** neighbourhood, and
`flowCkPred_step`'s box is built from the augmented flow's own IH neighbourhood — so this
route shrinks the domain with `n`.

However, the stronger fixed-box ODE theorem is already present and verified:

- `IsLocalFlow.contDiffOn_top`
  (`DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/ContDiffOnTop.lean`);
- `IsLocalFlow.contDiffOn_top_local`
  (`DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/ContDiffOnTopChartLocal.lean`).

Planner check passed for `ContDiffOnTop.lean`, and `#print axioms` for both the global and
local top-order flow theorems is clean (`propext`, `Classical.choice`, `Quot.sound` only).
So the next frontier is **not** a new linear-ODE smoothness theorem.  It is the wiring
frontier:

1. apply `IsLocalFlow.contDiffOn_top_local` to the geodesic chart-phase flow of
   `chartPhaseVF` on the existing nesting box;
2. package this as the missing `combined_inf` chart-flow theorem;
3. push through the existing off-zero bridge to obtain forward `expMap ContMDiffAt ∞` /
   `ContDiffOn ℝ ⊤` on a uniform ball.

The inverse `normalChartAt`/`expMapDiffeo : PartialDiffeomorph … ∞` upgrade remains the
next downstream inverse-function-theorem wiring step after the forward theorem lands.

## UPDATE (2026-06-13): forward `expMap C∞` LANDED

Steps 1–3 above are DONE: `Geodesic.exists_chartPhase_contDiffOn_isLocalFlow_combined_inf`
(`SmoothFlow.lean`) + `expMap_contMDiffAt_infty_of_norm_lt` (`OffZero.lean`) — `expMap` is
`ContMDiffAt ∞` on a **uniform** ball, axiom-clean (`[propext, Classical.choice,
Quot.sound]`). See `Geometry/Exponential/Smoothness/OffZero.md`.

The two Step B `hsmooth` hypotheses are now gated on **geometry/IFT wiring**, not the ODE
frontier:
- B-metric `normalCoordMetric_contDiffOn`: forward `expMap C∞` + a model-coordinate
  `mfderiv`-pullback-section smoothness brick (~100 lines, geometry layer).
- B-trans `normalTransition_contDiffOn`: the `C∞` inverse function theorem for the
  inverse chart `normalChartAt = (expMapDiffeo).symm` (separate frontier).

## UPDATE (2026-06-13): B-metric producer steps 1–2 LANDED in `StepBInputs.lean`

Two verified, axiom-clean (`[propext, Classical.choice, Quot.sound]`) building blocks for
`normalCoordMetric_contDiffOn`:
- `expMapDiffeo_contMDiffOn_ball` — the **C¹→C∞ comparison** (hard-stop #1 fallback): on
  `ball 0 δ ∩ source` (δ from `expMap_contMDiffAt_infty_of_norm_lt`), the realized
  `expMapDiffeo` (a `PartialDiffeomorph … 1`) is `ContMDiffOn ⊤`, since it agrees there with
  the now-`C∞` `expMap` (`ContMDiffOn.congr` + `expMapDiffeo_apply_eq`).
- `normalCoordMetric_apply` — the **scalar evaluation**
  `normalCoordMetric Y x z v w = g.inner(expMapDiffeo z)(D z v)(D z w)`, `D = mfderiv …`.

### DONE: full producer `normalCoordMetric_contDiffOn` (2026-06-13), axiom-clean
The full producer landed in `StepBInputs.lean` (focused check green,
`[propext, Classical.choice, Quot.sound]`).  Steps 3–5 were assembled exactly as scoped:
- step 3 pushforward sections: `expMapDiffeo_pushforward_section_contMDiffOn` (private) via
  `ContMDiffOn.contMDiffOn_tangentMapWithin` ∘ the constant tangent section
  `contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const` (NOT the homeomorph-symm route —
  that hits the `ModelProd`/`prodChartedSpace` instance wall) + `mfderivWithin_of_isOpen`;
- steps 4–5: `ContMDiffOn.clm_bundle_apply₂` (metric section + two pushforward sections) →
  `contMDiffWithinAt_totalSpace` scalar extraction → `contDiffOn_clm_apply` ×2 →
  `contMDiffOn_iff_contDiffOn`.

**`hsmooth` is no longer the gate.**  For a fixed `β`, `exists_metricLimit_normalCoord`'s
`hsmooth : ∀ k, ContDiffOn ℝ ⊤ (normalCoordMetric (X.obj k) (c k)) U` is now PROVABLE on the
producer's own ball `ball 0 δ_k ∩ source_k` from `normalCoordMetric_contDiffOn`.  The ONLY
remaining gap to discharge `hsmooth` on the wrapper's fixed `U` is **gap #2 (uniform radius)**:
the producer yields a per-`k` existential `δ_k`, while `exists_metricLimit_on` needs a single
`U` with `U ⊆ ball 0 δ_k ∩ source_k` for all `k`.

## UPDATE (2026-06-13, session 3): pure-ball producer LANDED; uniform-radius is NOT pure bookkeeping

`normalCoordMetric_contDiffOn_ball` landed in `StepBInputs.lean` (focused check green,
axiom-clean `[propext, Classical.choice, Quot.sound]`): combining `normalCoordMetric_contDiffOn`
with `Metric.isOpen_iff` on the open `expMapDiffeo.source` (`zero_mem_expMapDiffeo_source`), it
gives `∃ r > 0, ContDiffOn ℝ ⊤ (normalCoordMetric Y x) (Metric.ball 0 r)` — the clean pure-ball
shape (no `∩ source`), matching `NormalCoordMetricBoundInput.radius`.  This is the "smallest
domain/radius lemma" of the bridge route.

**Correction to the earlier note (it was too optimistic).**  Discharging `hsmooth`/`hdom` on a
fixed `U` is **HARD-STOP #1**, and the missing input is *not* pure Step-A bookkeeping — it is a
**smoothness-layer anchoring theorem**.  Precise reason:
- The producer radius `r_k = min(δ_k, source-ball_k)`, where `δ_k = (T_match/2)·ρ` comes from
  `expMap_contMDiffAt_infty_of_norm_lt` ⟵ `exists_unified_chartFlow_data_inf` — an **opaque ODE
  existential** with NO geometric anchor and NO uniform lower bound across the sequence.
- Step-A *does* uniformly control the **injectivity radius** (`InjRadiusDecayInput.decay`,
  `a·(min baseInj.ρ 1)^n·e^{-C·dist}`) and the **C²/geometry radius** `expMapC2Radius`
  (`GoodCoveringItem3.Item3RadiusInput`'s `ρ k α ≤ expMapC2Radius`, with
  `ball 0 (expMapC2Radius) ⊆ source`).  But `expMapC2Radius` is built from a *separate*
  `Classical.choose (expMap_contMDiffAt2_of_norm_lt)` (only **C²**), independent of the ∞-radius
  `δ_k`.  No theorem relates `δ_k` to `injRadius` or `expMapC2Radius`.
- Therefore `inf_k δ_k > 0` cannot be established, so `U ⊆ ball 0 δ_k` (fixed `U`, all `k`) is
  unprovable from current API.

**Exact missing theorem (the unblock):** a *named-radius* ∞-smoothness producer
`expMap_contMDiffAt_infty_of_norm_lt_radius : ‖w‖ < ρ_geom g p → ContMDiffAt ∞ (expMap g p) w`,
where `ρ_geom` is a geometric radius that Step-A already bounds below uniformly — e.g.
`ρ_geom = expMapC2Radius g p` (then `ball ⊆ source` is free via its 4th component), or a fixed
fraction of `injRadius g p`.  Equivalently: prove the ∞-smoothness radius `≥ expMapC2Radius`
(plausible since the C² radius is itself a downgrade of the same fixed-box chart-flow `C∞`
data, but the two existentials are chosen independently, so this needs an explicit comparison
or a re-derivation of the ∞ producer anchored to `expMapC2Radius`).  This is **smoothness-layer
work** (re-opening / extending the OffZero off-zero ∞-smoothness frontier), NOT the
domain-bookkeeping the planner's framing assumed.  Once it lands, the fixed-`U` discharge
chains: `normalCoordMetric_contDiffOn_ball` (now on `ball 0 (expMapC2Radius)`) + Step-A
`Item3RadiusInput`/`InjRadiusDecayInput` uniform lower bound + `ContDiffOn.mono`.

The ODE/geometry smoothness frontier for a *single* manifold is closed; what remains is making
that single-manifold smoothness radius **geometrically named and uniformly bounded below**.

## UPDATE (2026-06-13, session 4): unblock plan VERIFIED feasible; execution blocked on a concurrent agent holding `GaussLemmaPullback.lean`

Audited the OffZero/GaussLemmaPullback smoothness-radius layer.  **Hard-stop #1 does NOT trigger** —
the C∞ data IS recoverable, and the unblock is a clean, small change (NOT a smoothness-framework
rewrite).  Key findings:

1. `expMapC2Radius` (`GaussLemmaPullback.lean:230`) = `min` of four `Classical.choose` radii:
   component **1** = `expMap_contMDiffAt2_of_norm_lt` (C²), 2 = radial-geodesic, 3 = rescale,
   4 = `exists_metric_ball_subset_expMapDiffeo_source` (⇒ `ball 0 expMapC2Radius ⊆ source`, FREE).
   `expMapC2Radius_pos` and the geometry/`_radius` consumer lemmas use it **opaquely** (positivity +
   `min_le_*`), so changing component 1's *source theorem* is safe.
2. The C² radius (`expMap_contMDiffAt2_of_norm_lt`, OffZero:670, via `exists_unified_chartFlow_data_two`
   ⟵ `..._combined_two`) and the ∞ radius (`expMap_contMDiffAt_infty_of_norm_lt`, OffZero:1171, via
   `exists_unified_chartFlow_data_inf` ⟵ `..._combined_inf`) are **parallel** fixed-box chart-flow
   producers — same shape `∃ δ>0, ∀ w, ‖w‖<δ → ContMDiffAt … LEVEL`.  So `expMap_contMDiffAt_infty_of_norm_lt`
   ALREADY supplies the C∞ data; nothing new in the ODE layer is needed.
3. Bare `expMap_contMDiffAt2_of_norm_lt` is consumed ONLY in `GaussLemmaPullback.lean` (lines 231,
   247, 262 — the radius def, `_pos`, and the `_radius` lemma).  `expMap_contMDiffAt2_of_norm_lt_radius`
   has many downstream **C²** consumers (JacobiVariation, MinimizingGeodesic, GaussLemmaPullback) — must
   stay C².

### READY-TO-EXECUTE plan (Option X — minimal, all in `GaussLemmaPullback.lean`)
- L231 & L246-247: swap component-1 theorem `Exponential.expMap_contMDiffAt2_of_norm_lt` →
  `Exponential.expMap_contMDiffAt_infty_of_norm_lt`.  (`expMapC2Radius` keeps positivity + `ball⊆source`;
  value may shift but every consumer is opaque.)
- L256-263 `expMap_contMDiffAt2_of_norm_lt_radius`: keep its `ContMDiffAt 2` conclusion, but the
  swapped `(Classical.choose_spec …).2 w …` now yields `∞`, so append `.of_le ENat.LEInfty.out`
  (the codebase's ∞→finite idiom, used at OffZero:919/961/1192/1225).
- ADD `expMap_contMDiffAt_infty_of_norm_lt_radius (hw : ‖w‖ < expMapC2Radius g p) : ContMDiffAt ∞ … w :=
  (Classical.choose_spec (Exponential.expMap_contMDiffAt_infty_of_norm_lt g p)).2 w
    (lt_of_lt_of_le hw (min_le_left _ _))`.
- Update the `expMapC2Radius` docstring (L226) "C² radius" → "C∞ smoothness radius".
- (alt **Option Y**, if touching the radius def is disallowed: instead strengthen
  `expMap_contMDiffAt2_of_norm_lt` itself to `∞` in OffZero — but it must move below the ∞ theorem
  and STILL forces the same L262 `.of_le` edit in GaussLemmaPullback; Option X is strictly cleaner.)

Then downstream (own files, unblocked once the above lands):
- `StepBInputs.lean`: add `normalCoordMetric_contDiffOn_geom : ContDiffOn ℝ ⊤ (normalCoordMetric Y x)
  (Metric.ball 0 (expMapC2Radius Y.metric x))` — like `normalCoordMetric_contDiffOn_ball` but with the
  NAMED radius: `expMapDiffeo_contMDiffOn_ball`'s `∩ source` is absorbed by component 4, and ∞-smoothness
  now holds on the whole `expMapC2Radius` ball via `expMap_contMDiffAt_infty_of_norm_lt_radius`.
- `StepBLocalMetrics.lean`: discharge `hsmooth`/`hdom` of `exists_metricLimit_normalCoord` for fixed β
  using Step-A `Item3RadiusInput` (`ρ k α ≤ expMapC2Radius`, uniform) + `ContDiffOn.mono`, with
  `U = ball 0 (uniform ρ)`.

### BLOCKER (operational, not mathematical)
`GaussLemmaPullback.lean` is held by a concurrent agent (token `ba8d2152`), actively running successive
`check`s.  Changing it directly, or changing its upstream `OffZero.lean` in a way that breaks its
in-flight checks (Option Y), would disrupt that agent.  Per the multi-agent rules the lock was NOT
force-released.  Resume Option X above once `GaussLemmaPullback.lean` is free.

## UPDATE (2026-06-13, session 5): Option X EXECUTED — frontier-1 (named-radius ∞ smoothness) CLOSED

HARD-STOP #1 is resolved. The smoothness radius is now geometrically named and the metric producer
is anchored to it.  All focused checks GREEN; the three new endpoints are **axiom-clean**
(`propext, Classical.choice, Quot.sound`, no `sorryAx`).

**`GaussLemmaPullback.lean` (Option X, verbatim):**
- `expMapC2Radius` component **1** swapped `expMap_contMDiffAt2_of_norm_lt` → `…_infty_of_norm_lt`
  (`expMapC2Radius_pos` branch updated; value may shift but every consumer is opaque — `min_le_*` /
  positivity only; the `ρ ≤ expMapC2Radius` discipline in GoodCoveringItem3 is an *upper-bound
  hypothesis on ρ*, unaffected).
- NEW `expMap_contMDiffAt_infty_of_norm_lt_radius (hw : ‖w‖ < expMapC2Radius g p) : ContMDiffAt ∞ … w`.
- `expMap_contMDiffAt2_of_norm_lt_radius` kept `ContMDiffAt 2`, now derived `∞ → 2` via
  `.of_le (WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤))` (the order is `WithTop ℕ∞`; `∞ ≠ ⊤`, so plain
  `le_top` fails — this is the working idiom, cf. `Curvature/Riemann/Basic/Field.lean:145`).
- NEW adapter `mem_expMapDiffeo_source_of_norm_lt_radius` (ball ⊆ source, extracted from
  `mem_expDomain_of_norm_lt_radius`'s inline derivation; that proof now reuses it).

**`StepBInputs.lean` (downstream, named-radius producers):**
- Refactor: extracted the reusable core `normalCoordMetric_contDiffOn_of_smooth (hU : IsOpen S)
  (hf : expMapDiffeo C∞ on S) : ContDiffOn ⊤ (normalCoordMetric Y x) S`; `normalCoordMetric_contDiffOn`
  is now a 3-line specialization (no duplicated bundle proof).
- NEW `expMapDiffeo_contMDiffOn_expBall` and `normalCoordMetric_contDiffOn_expBall` — the planned
  `…_geom`: `ContDiffOn ℝ ⊤ (normalCoordMetric Y x) (Metric.ball 0 (expMapC2Radius Y.metric x))`,
  the `∩ source` absorbed by component 4 (`mem_expMapDiffeo_source_of_norm_lt_radius`), ∞-smoothness
  on the whole named ball via `expMap_contMDiffAt_infty_of_norm_lt_radius`.
- NEW `hsmooth` reducer `contDiffOn_normalCoordMetric_of_subset_expBall`: given `hsub : ∀ k,
  U ⊆ ball 0 (expMapC2Radius (X.obj k).metric (c k))`, produces the `∀ k, ContDiffOn ⊤ … U`
  hypothesis of `exists_metricLimit_normalCoord` by `.mono`.  Reduces `hsmooth` to the single
  containment `hsub`.

### REMAINING frontier (the β-wrapper, `StepBLocalMetrics.lean`) — planner-scoped Step-A wiring
`exists_metricLimit_normalCoord` still needs, for a concrete sequence, the fixed `U` + `hdom` + `hsmooth`:
- pick `U = ball 0 ρ` with `ρ` the uniform covering radius (book `205 e^{20cC} λ^α`, fixed across `k`);
- `hsub`/`hsmooth`: from `Item3RadiusInput` (`ρ k α ≤ expMapC2Radius (X.obj k).metric c`, uniform) feed
  `contDiffOn_normalCoordMetric_of_subset_expBall`;
- `hdom`: `U ⊆ ball 0 (input.radius k (c k))` — needs the `NormalCoordMetricBoundInput.radius` uniform
  lower bound (gap #2: a `radius_lb` field or a Step-A lemma giving the uniform `R`).
This is the "full Step-A β wiring" the planner flagged as a separate follow-up; it is now pure assembly
(no remaining smoothness/geometry frontier), gated only on the honest-input `radius_lb`/Item3 wiring.
