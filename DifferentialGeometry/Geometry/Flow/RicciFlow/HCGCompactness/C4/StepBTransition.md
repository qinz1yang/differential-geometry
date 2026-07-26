# StepBTransition.lean — B-trans transition limits + cocycle (`lbl394` transition, 2026-06-13)

## UPDATE 2026-07-18 — canonical framed source repair

`NormalOverlapOn` now records the actual framed chart domain:
`framedExpDiffeo x` source membership followed by `framedChartAt y` source
membership.  The lower-layer `StepBInputs.framedChart_smooth` transports the
existing raw inverse-chart smoothness through the fixed orthonormal frame;
this file only consumes that canonical producer.  `contDiffOn_normalTransition`
now consumes `expRadiusGp` balls plus a
`framedExpDiffeo x`-to-`framedExpMap y` image containment.  The public
`normalTransition` name is retained where it deliberately packages the
per-object manifold instances; its definition is the canonical
`framedTransition`.

`exists_trans_h6` now asks for `expRadiusGp` containments.  After the canonical
dependency chain was refreshed in order, this file passed focused verification
with the lower `framedChart_smooth` producer and the migrated H6
`normal_bounds_on` interface.  The earlier stale-artifact diagnostics are
resolved; there is no remaining source or verification blocker in this file.

Accounting: this file's framed source repair and verification are 100%
complete.  Together with the overlap file this is 2/29 audited migration files
repaired and verified; it does not change the 0% textbook B1 theorem or the 0%
unconditional endpoint theorem.  Dedicated transition machinery in these two
files is 100%; whole-HCG machinery remains about 60%.

## UPDATE 2026-06-22 — transition `C∞` DONE; `hsmoothJ`/`hsmoothJbar` frontier discharged

The `C∞`-chart-inverse frontier described in the 2026-06-21 passes is **resolved** (verified,
targeted build green, no new `sorry`). The fresh IFT-at-∞ was done in `StepBInputs.lean`:
`normalChartAt_contMDiffAt_infty` (pointwise) + `normalChartAt_contMDiffOn_infty` (on the named
image `expMap g p '' ball 0 (expMapC2Radius g p)`). Route as planned, but with two refinements
discovered while building:
- The per-point invertible derivative was obtained NOT from the `TangentSpace`-typed `mfderiv`
  composite (that hit a `TangentSpace 𝓘(ℝ,E) (χ q) = E` defeq wall in the `HasFDerivAt`
  derivative slot) but from `(fderiv ℝ (extChartAt q ∘ expMap) v₀).IsInvertible` — `fderiv` on
  an `E → E` map is genuinely `E →L E`-typed, so the equiv is a literal `E ≃L E`. Key lemmas:
  `isInvertible_mfderiv_extChartAt` (general source point), `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv`
  (from `exp_isLocalDiffeomorphOn_ball`), `ContinuousLinearMap.IsInvertible.comp`,
  `ContDiffAt.to_localInverse` at `∞`, `hasMFDerivAt_iff_hasFDerivAt`.
- The local-inverse↔`normalChartAt` identification used the clean `normalChartAt_symm_apply` /
  `_left_inv` / `_right_inv` lemmas (raw `PartialDiffeomorph` coercions don't normalize).

Then in this file: `contDiffOn_normalTransition` (the bridge: forward `expMapDiffeo x` `C∞` on
`U` ∘ chart inverse `normalChartAt y` `C∞` on the image, via `ContMDiffOn.comp`), and
`exists_transitionLimit_normalTransition` was rewired to DROP `hsmoothJ`/`hsmoothJbar`, taking
instead the honest geometric inputs `hUx`/`hVy` (domain ⊆ forward `expMapC2Radius` ball) and
`hmapsJ`/`hmapsJbar` (`expMapDiffeo` carries the domain into the other centre's normal nbhd).
No `.lean` consumers of the wrapper, so the signature change is safe.

**Soundness note:** the result rests on `expMap_contMDiffAt_infty_of_norm_lt` (forward ball-`C∞`).
Grep-traced: that route (`exists_unified_chartFlow_data_inf`) does NOT use the 3 known
`ChainedFlowContinuity` sorries — those feed only the orthogonal off-zero
`expMap_contMDiffAt_of_ne_zero`. Same clean foundation as the (accepted) metric side. A
definitive `#print axioms` was not run (would need a full build).

**Remaining for full `lbl394`:** only the uniform-radius / overlap Step-A wiring (a single
`U`/`V` with the `hUx`/`hVy`/`hmaps*` containments across the sequence) — geometric input from
bounded geometry + inj-radius, NOT analysis. `lbl397` stays gated on Step C.

## UPDATE 2026-06-21 — `hsmoothJ` is a GENUINE frontier (unlike the metric side); architecture pinned

The metric-side smoothness gap was closable from the FORWARD exp `C^∞` alone (see
`StepBLocalMetrics.md` update). The transition side is **not** the same: `normalTransition Y x y =
normalChartAt y ∘ expMapDiffeo x`, and `normalChartAt y` is the chart INVERSE
(`expMap⁻¹`). Currently only `C^1` exists (`NormalCoordinates.normalChartAt_contMDiffOn`
is `ContMDiffOn … 1`), so the composite is capped at `C^1`. Upgrading needs the `C^∞`
manifold inverse-function theorem: exp `C^∞` (have) + `d exp` nonsingular on the ball
(item-3 B3 `ExpNonsingular`) ⟹ inverse `C^∞`.

**Architecture obstruction (the important finding).** The `C^∞` inverse CANNOT be obtained
by bumping `LocalDiffeomorphism.lean` from order 1 to ∞, because the `C^∞` forward exp fact
(`Smoothness/OffZero.expMap_contMDiffAt_infty_of_norm_lt`) is **downstream** of
`LocalDiffeomorphism` in the import DAG:
`LocalDiffeomorphism` → `ChartFlow/ChainedFlowContinuity` → `Smoothness/OffZero`. Adding
`import OffZero` to `LocalDiffeomorphism` is a cycle (confirmed: mass "already declared"
errors). The C^1 local diffeo is literally used to BUILD the C^∞ forward smoothness.

**Route for the next session (fresh derivation, downstream).** Build the `C^∞` chart inverse
in a file downstream of BOTH `OffZero` and `NormalCoordinates` — `StepBInputs.lean` is ideal
(it already imports both and already has the forward `normalCoordMetric_contDiffOn_expBall`).
Re-run the pointwise IFT at ∞ there (do NOT touch `LocalDiffeomorphism`):
1. `chartedExp y := extChartAt I y ∘ expMap y`, prove `ContDiffAt ℝ ∞` at `0` from
   `expMap_contMDiffAt_infty_of_norm_lt_radius` + `contMDiffAt_extChartAt` + `.contDiffAt`.
2. `HasFDerivAt chartedExp (id) 0` from `mfderiv_expMap_at_zero` + `mfderiv_extChartAt_self`
   (both public).
**CRUCIAL `∞`-nbhd subtlety (found 2026-06-21, second pass).** `ContDiffAt.to_localInverse`
at `∞` gives `ContDiffAt ℝ ∞ localInverse (chartedExp 0)` — at the SINGLE point only. You
CANNOT then extract `ContDiffOn ℝ ∞` on a neighbourhood: `ContDiffAt.contDiffOn`
(Mathlib `…/ContDiff/Defs.lean`) has side condition `m = ∞ → n = ω`, so `ContDiffAt ∞`
yields only `ContDiffOn k` on a (shrinking) nbhd for each finite `k`, never a single
`ContDiffOn ∞` nbhd (that needs analyticity `n = ω`). The forward metric side dodged this
because `expMap_contMDiffAt_infty_of_norm_lt_radius` gives `ContMDiffAt ∞` at EVERY point of
the ball, and pointwise-`ContMDiffAt ∞` on an open set DOES assemble to `ContMDiffOn ∞`.
Therefore the inverse must be done the SAME way: prove `ContMDiffAt ∞ (normalChartAt y) q`
at EVERY `q` in the open image, not via a single IFT at `0`.

3. (corrected) For each `q ∈ expMapDiffeo y '' (ball 0 r)` (`r = expMapC2Radius y`), set
   `v := normalChartAt y q ∈ ball 0 r`. Apply `ContDiffAt.to_localInverse` to `chartedExp y`
   AT `v` (not at 0): need (i) `ContDiffAt ℝ ∞ (chartedExp y) v` (from
   `expMap_contMDiffAt_infty_of_norm_lt_radius` at `v` since `‖v‖ < r`), and (ii)
   `HasFDerivAt (chartedExp y) (e : E ≃L E) v` with `e` INVERTIBLE — this is the new work: at
   general `v` the derivative is not `id`. Get invertibility from
   `Comparison.ExpBallDiffeo.exp_isLocalDiffeomorphOn_ball` (whole-ball nonsingularity, C^1
   local diffeo at each ball point) → `IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv`
   (cf. `Curvature/PullbackNaturality.lean:78`) for `d exp_y v`, composed with `d extChartAt`
   (also an equiv), to assemble the `E ≃L E` fderiv of `chartedExp y` at `v`.
   (`(∞ : WithTop ℕ∞) ≠ 0` via `(by decide)`; `show … from 0` blocks `rw [expMap_zero]` — it
   elaborates to `have this := 0; this`, so use `simp only`/`conv`.)
4. Identify: `normalChartAt y q = localInverse_v (extChartAt y q)` near `q`
   (`normalChartAt_left_inv`, `expMapDiffeo_apply_eq`), giving `ContMDiffAt ∞ (normalChartAt y) q`.
   Range over the open image ⟹ `ContMDiffOn I 𝓘(ℝ,E) ∞ (normalChartAt y)
   (expMapDiffeo y '' ball 0 r)` — a NAMED domain (clean wiring, like the metric side).
5. Then `normalTransition` `C^∞` on `U` follows (compose forward `expMapDiffeo x` `C^∞` with
   `normalChartAt y` `C^∞`), given a containment `expMapDiffeo x '' U ⊆ expMapDiffeo y '' ball 0 r`
   — an honest overlap input (strengthen `NormalOverlapOn`). Finally rewire
   `exists_transitionLimit_normalTransition` to drop `hsmoothJ`/`hsmoothJbar` (like the metric
   side dropped `hsmooth`), keeping only the containment inputs.

This is a **~2–3 hr** standalone IFT-at-∞ brick (the per-point invertible-derivative-equiv
construction at general `v` is the real plumbing). It does not reduce to new mathematics — only
to re-running, downstream and at ∞ pointwise over the ball, what `LocalDiffeomorphism` did at
C^1 at the centre. The cheaper "IFT at 0 only → nbhd" route does NOT work (see the `∞`-nbhd
subtlety above).

## Status: generic theorem COMPLETE; HCG `normalTransition` wrapper blocked on `C^∞` smoothness

**Verification PASSED**: focused check + targeted build green (no warnings); axiom-clean
(`[propext, Classical.choice, Quot.sound]`) for `exists_transitionLimit_on`.

## Delivered
- `exists_transitionLimit_on` — transition-map limits + limit cocycle, generic
  model-coordinate form. Transition maps `J k : U → E`, `J̄ k : V → E` on nested **open
  Euclidean domains of the same model `E`** (`E^α, Ē^β ⊆ E`), each `C^∞` on its domain,
  satisfying `IsometryDerivBoundsOn` and mutually inverse, get a subsequence with limits
  `Jinf`, `J̄inf` converging in `C^∞` on compacts plus the **limit cocycle**
  `J̄inf (Jinf x) = x` / `Jinf (J̄inf y) = y` — stated **conditionally on domain
  membership** (`Jinf x ∈ V`, `J̄inf y ∈ U`), as in `isometry_seq_diffeo_on`.

This is the `F = E` instance of `isometry_seq_diffeo_on` (B-loc) in transition language —
the book's `lbl394` transition endpoint. No new proof content beyond B-loc; it packages
the same-model-space case under the `J`/`J̄` cocycle names that B-Falpha/B-glue cite.

## Orientation note
Lean types fix the composition order: the cocycle output of `isometry_seq_diffeo_on` is
`J̄inf ∘ Jinf = id` on `U` (conditional `Jinf x ∈ V`) and `Jinf ∘ J̄inf = id` on `V`
(conditional `J̄inf y ∈ U`). The book's `J̄_∞^{βα} ∘ J_∞^{αβ} = id_β` (line 1494) matches
the first with `J := J^{αβ}` (domain `E^α`-side `U`), `J̄ := J̄^{βα}` (domain `V`).

## HCG `normalTransition` wrapper DELIVERED by honest exposure (2026-06-13, frontier-1)

`exists_transitionLimit_normalTransition` (new `section HCGNormalTransition`) wires
`normalTransition` + `ExpInverseDerivBoundInput` + center sequences `x y : ∀ k, (X.obj
k).M` into `exists_transitionLimit_on`. **Verification PASSED** (focused check + targeted
build green; axiom-clean `[propext, Classical.choice, Quot.sound]`). Fixed-pair only, NOT
the finite diagonal over all `α, β`.

Honestly-exposed explicit hypotheses (bare, not renamed):
- `hsmoothJ/hsmoothJbar : ∀ k, ContDiffOn ℝ ⊤ (normalTransition …) U/V` — the genuine
  smoothness; blocked on the **same foundational gap** as B-metric (`expMap` `ContMDiffAt
  ∞` on a uniform ball; the realized `expMapDiffeo` is `C^1`). One upstream fix unblocks
  both wrappers.
- `hovlJ/hovlJbar : ∀ k, NormalOverlapOn (X.obj k) (x k) (y k) U` — new honest
  domain/overlap predicate (the bare condition `z ∈ exp_x.source ∧ exp_x z ∈
  normalChart_y.source` on `U`), bridging `ExpInverseDerivBoundInput`'s overlap bound
  (`input.exp_inv_deriv`, `M = input.derivC r`) to `IsometryDerivBoundsOn U`.
- `hLeft/hRight` — the cocycle, **conditional on `U`/`V`** (the overlap), never global
  (`normalTransition` is junk off the overlap).

### Conditional-cocycle generalization of B-loc (required, this push)
`comp_eq_id_of_cInf_on` and `isometry_seq_diffeo_on` (StepBLocalizedAA) and
`exists_transitionLimit_on` had **global** inverse hypotheses (`∀ k x, …`), which
`normalTransition` cannot satisfy. Generalized them to **domain-conditional** (`∀ k, ∀ x
∈ U, …`) — the honest form matching their already-conditional conclusions. Backward
compatible (the only caller threaded the membership through). All re-verified axiom-clean.

## 2026-07-13 H6 fixed-pair entrypoint

Added `exists_trans_h6`. It feeds localized H6 metric and exponential-radius
bounds, smoothness, overlap, and coordinate maps-to data into
`H6Isometry.normal_bounds_on` for both transition directions, then reuses the
existing generic transition-limit extractor. It does not consume
`ExpInverseDerivBoundInput` and introduces no replacement input structure.

The canonical interface now separates convergence domains `U`, `V` from open,
bounded target-anchor sets `Ua`, `Va`.  Forward bounds use source domain `U`
and target anchor `Va`; reverse bounds use source domain `V` and target anchor
`Ua`.  Metric and exponential-radius containments are required for both source
domains and anchors, while transition `MapsTo` lands in the anchors.  The limit
cocycle output remains conditional on membership in the convergence domains
`U`, `V`.  Focused verification and the targeted refresh passed.

After its sole downstream compatibility caller was removed, a live search found
no remaining consumer of the old S6 fixed-pair entrypoint.  That declaration was
removed; `exists_trans_h6` is now the canonical fixed-pair producer. Focused
verification and the targeted refresh passed.
