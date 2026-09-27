# OPUS fill log T4A: the T4′ final assembly `fineCutNeckSupplyStrong_holds` (2026-09-26)

Worker lane T4A. Scope: assemble `FineCutNeckSupplyStrong P₀ g₀` (`Surgery/Contract/FineCutNeckSupplyStrong.lean`,
SL2 / DESIGN_S_SUPPLY §1(A) T4′) from the delivered consumer waves SC1–SC8, T1 and the tolerances. New files only;
read-only compiles (`LEAN_NUM_THREADS=4 lake env lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true`);
uncommitted imports through scratch modules under the session scratchpad `t4a/` (SC8's rename scheme `SC8.<Base>`,
SC8's oleans copied, the remaining suppliers compiled into `t4a/olean/SC8/`, one lean at a time). No git writes, no
lake build, no root-aggregate edit, no committed file modified, no other lane's file modified.

## Progress

- read AGENTS.md (pc3: imports first, no header, no module docstring, zero comments), SC1–SC8 logs, SL1/SL2/SP1/SP2
  logs, H13/H17/H18/H20 digests, DESIGN_S_SUPPLY §1(A)/§3, DESIGN_STRONG_INTERFACE §2, HANDOFF_20260927.
- supplier survey (all on disk, none in the root aggregate): SC8's four files exist and have no `sorry`
  (`HistoryStrongNeckTopSliceTracedRegion` = SC8-5a, `TracedRegionTimeZeroUniformBound` = SC8-5b,
  `TracedRegionWindowLimit` = SC8-1, `ScaledPointedLimitLine` = SC8-2); SC8-4a/4b (the ℝ×N capture at every slice of
  the window limit = the per-layer supply at depth `T > 0`) and SC8-3 (simple connectivity) had NOT landed at the
  time of this survey. CORRECTION (lead, watcher cycle 3; SC8 CLOSED since): SC8-3 = `Geometry/Neck/
  LineNeckSimplyConnected.lean` (`SpatialNeck.simplyConnectedSpace_of_line`), SC8-4a = `LocalPullProductNeck`, SC8-4b =
  `TracedRegionWindowProductNeckSupply.lean` (`eventually_forall_neckAlternative_of_window_product_structure`), plus
  `LocalFlowLimitBaseScalar` ARE on disk; they are consumed by T4A-8 below.
- scratch chain `t4a/` (background, sequential): SC8's 25 oleans copied; XA4 ×2, SC7 ×8, SC2 ×5, SC4 ×5 (+X5c/X5d),
  SC6's `HistoryStrongNeckExtendHorizon`, SC8-5a/5b, SL2's def compiling in dependency order.

## Findings before the statements (failures first)

1. **The per-layer supply at depth `T > 0` is the only missing analytic input.** Everything else T4′ needs is on
   disk. SC8's own log (Findings 1, 2) records two DEVIATIONS from SC6-c's `hsupply` shape that the eventual SC8-4b
   supplier will carry: (a) its traced premise is UNIFORM in the radius (`∃ K, ∀ A T' ≤ T, …`), not `∀ A T', ∃ K`;
   (b) it covers slices of depth `T' < T` only (the window limit lives on `(−T, 0]`). Hence SC6-c as delivered
   cannot be fed by SC8-4b. DECISION (recorded before proving): a staggered variant of SC6-c is proved here (new
   file, SC6-c untouched): base case = top-slice supply (SC2-b, no premise), inductive step = deep supply at
   `T' = T − δ/2` from the traced region at depth `T` with uniform `K`, gain `δ/2` per step, `δ = (10·Qup)⁻¹`.
   SC6-c becomes a corollary (deferred merge).
2. **`R_L(xₙ)·sₙ → ∞` needs no new analysis**: `exists_pos_le_singular_incoming_time_of_initialIdentification`
   applied to the terminal slab (`hsing`, `hG`) with `∀ j, (event j).incoming.SingularEndpoint` from the records
   (`GeometricCutoffRecord.singular`, as SS2) gives `a(g₀) ≤ sₙ`; `R_L(xₙ) ≥ Kfineₙ → ∞`.
3. **Pinching needs no `a₀`**: `Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀`
   (committed, the body of `PinchingThroughSurgery.lean`) gives ONE `phi(P₀, g₀)` with `PhiAlmostNonnegative` on
   every slab whose initial metric is the stage's initial metric; `EventSlabsPinched phi` and the terminal-slab
   clause follow from the records and `hG`. T4′'s `InFixedHamiltonIveyRegion (initialMetric 0) a₀` binder is not
   consumed.
4. **Set transport to `extendAt`**: SC7-3b transports points, distances and scalars; the separation sets of SC4-c
   and the witness statements must reach the `stageAt` carrier of `H.extendAt`. One generic lemma
   `extendAt_stageAt_iff` transports ANY predicate `Q K g y` in `(stage, metric, point)` along the HEq of base
   points (same `generalize`/`subst` device as `scalar_ball_bound_extendAt_iff`); the sets are transported as
   the existence statement `∃ S V W : Set K.Carrier, …`.
5. **SC4-b wants exact-radius clauses for every real `A`**; the diagonal choice can only carry countably many. The
   clauses are chosen at integer radii `m + 1` and converted to any real `A ≤ m + 1` by SC4-a′
   (`exists_mem_riemannianEDistOf_eq_of_ball_diff_subset`, last crossing of the level `A`).
6. **Top-ball bounds at the slice**: the lower bound is SC7-2a at the slice `τₙ` (constant `1/(4(1+Cgrad·a)²)`, no
   `L`-transfer); the upper bound is SC7-1d's `L`-bound on the compact `L`-ball transported by
   `eventually_riemannianBallOf_subset_image_closedBall` (`G(τ)`-ball inside the `L`-closed-ball) and
   `eventually_scalar_close_on_compact`. The uniform `Qup` is SC8-5b along a subsequence.
7. **Horn containment of `L`-balls**: `subset_hornHalfRange_of_isPreconnected_of_scalar_gt` (SC7-1b) on the
   path-connected open `L`-ball with the gradient lower bound gives `ball_L(x, 4a/√R_L) ⊆ hornHalfRange`, which is
   SC2-b's compact `B` (closed `3a`-ball) input.

## Statements (recorded BEFORE proving; elaborated with `sorry` first)

**T4A-1 = pinching and the terminal time from the records** (`Surgery/Topology/HistoryPinchingOfCutoffRecords.lean`,
ns `…Surgery.Topology`): `exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords P₀ g₀ : ∃ phi, Admissible phi ∧
∀ H, InitialIdentification P₀ g₀ H.toHistory → ∀ {p₀ δ₀ ρ₀}, H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀ → H.EventSlabsPinched phi ∧
∀ k {s} (G : (H.stage k).IncomingSlab (H.time k) s), G.flow.base.metric (H.time k) = H.initialMetric k →
PhiAlmostNonnegative G.flow (Ico (H.time k) s) phi`; `exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords P₀ g₀ :
∃ a > 0, ∀ H, InitialIdentification … → hasCanonicalCutoffRecords … → ∀ k {s} G, initial-metric equation → G.SingularEndpoint →
a ≤ s`. PROVED (Finding 2, 3), clean.

**T4A-2 = generic transport along `extendAt`** (`Surgery/Topology/RetainedCoreHistoryExtendAtStageTransfer.lean`, ns
`…RetainedCoreHistory`): `extendAt_stageAt_iff H hend G hG hat hts (Q : ∀ K : OrientedThreeStage, SmoothRiemannianMetric
ThreeModel K.Carrier → K.Carrier → Prop) (y) (yh) (hy : HEq yh y) : Q (Hext.toHistory.stageAt t') (Hext.toHistory.stageMetric
(activeStage t') t') yh ↔ Q (H.stage last) (G.flow.base.metric t) y` (`Hext = H.extendAt …`, `t' = H.extendAtTime …`).
PROVED (Finding 4), clean.

**T4A-3 = B13-style inputs on `extendAt`** (`Surgery/Topology/RetainedCoreHistoryExtendAtLimitInputs.lean`):
`extendAt_traced_limit_inputs H hend G hG hat hτs hpinch hpinchG hderiv hderivG hclass hcanG hnc hncG` = the conjunction of
B13's `hnc` (with `t₀ := t'`, `ρ := ε`), `hpinch`, `hwit` (constants `ε C1 C2`, threshold `qcan`), `hderiv` on
`H.extendAt hend G hG hat hτs` at `t' = extendAtTime` (SC6-d's inline discharges as one lemma). PROVED, clean.

**T4A-4 = SC6-c′, the staggered depth induction** (`Surgery/Topology/HistoryStrongNeckStaggeredDepthInduction.lean`, ns
`…RetainedCoreHistory`): `exists_isTracedRegion_of_forall_neckAlternative_of_staggered_supply` = SC6-c with `hsupply`
replaced by `htopneck` (SC8-5a's `hneck`: every class witness at the points of the top-slice ball above `c·Rₙ` is a neck) and
```lean
    (hdeep : ∀ T : ℝ, 0 < T →
      (∃ K : ℝ, 0 ≤ K ∧ ∀ A T' : ℝ, 0 < A → 0 < T' → T' ≤ T → ∀ᶠ n in atTop,
        (H n).toHistory.isTracedRegion (t n) (y n) (A / √(R n)) (T' / R n) (K * R n)) →
      ∀ T' : ℝ, 0 ≤ T' → T' < T → ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in atTop, <SC6-c's supply body at depth T'>)
```
conclusion = B13's `htraced` verbatim. Route: `δ := (10·Qup)⁻¹`, `K := 8√3(1+φ1+φ0)·Qup` (uniform); `step T'`: supply
at `T'` ⇒ SC6-b at `T'` ⇒ traced at `T' + δ` with bound `K`; base `T' = 0` from `htopneck` (the top-slice trace is the
singleton, SC8-5a's device); `claim m`: traced at depth `δ + m·δ/2` uniformly ⇒ `hdeep` at `T := δ + m·δ/2` with
`T' := T − δ/2` ⇒ `step` ⇒ depth `δ + (m+1)·δ/2`; then `mono_depth`. PROVED, clean.
This is the lead's blocker (WATCH_SC8 cycle 1, points (i)–(iii)): (i) `K` before `∀ A` in the premise, (ii) strict `T' < T`
with the `δ/2` stagger and the `T = 0` base, (iii) the supply is consumed in `∀ᶠ n` full-sequence form — the passage from
SC8-4b's subsequence form (`by_contra` + `Filter.extraction_of_frequently_atTop`, then SC8-1 on `H ∘ σ`) is done on
THIS side, inside T4A-8 (`exists_tolerance_eventually_neckAlternative_of_isTracedRegion_uniform`).

**T4A-5 = radius conversion of the separation clauses** (`Geometry/Metric/Distance/SeparatedSideBallClause.lean`, ns
`DifferentialGeometry.Geometry.Metric`): `separated_side_clause_of_le_radius` — from SC4-c's clause at radius `r` (cover of
the closed `3r`-ball, side points in `[r, 3r)`) and `b < A ≤ r`, SC4-b's clause at radius `A` (via SC4-a′, last crossing of
the level `A`). PROVED (Finding 5), clean.

**T4A-6 = slice geometry at a deep horn point** (`Surgery/Topology/HornPointSliceGeometry.lean`):
`IncomingSlab.quarter_scalar_le_on_closedBall_of_gradientBoundBefore` (slice `τ`: `R ≥ R(x)/(4(1+Cgrad·ρ)²)` on the closed
`ρ/√R(x)`-ball, SC7-2a), `TerminalLimitMetric.quarter_scalar_le_on_ball_of_gradientBoundBefore` (same in `L`, SC7-2b),
`TerminalLimitMetric.scalar_le_on_slice_ball_of_image_closedBall` (`L`-bound + ball capture + scalar closeness ⇒ slice
bound `Q + η`), `TerminalCorePresentation.riemannianBallOf_subset_hornHalfRange` (Finding 7). PROVED, clean.

**T4A-7 = the blow-up contradiction on `extendAt` sequences** (`Surgery/Topology/TerminalHornBlowupContradiction.lean`,
ns `…RetainedCoreHistory`): `exists_tolerance_false_of_deep_horn_sequence : ∃ epsW > 0, ∀ (H hend s τ G hG hat hτs y R),
…T4′ class data at `ε ≤ epsW`, `ε ≤ crossingNeckAccuracy`, `ε₁ ≤ 1/30000`, `qcan ≤ Cq·Rₙ`…, hballLow (∀ A, ∃ Qlow),
hballUp (∀ A, ∃ Qup(A)), htopneck, hdeep (the ∀-sequence form of the per-layer supply, instantiated at the class
constants), separation data (SC4-b's shape with `B = 7`), no `eps`-neck at `yₙ` → False`. Route: T4A-3 per `n`;
SC8-5a (top traced regions) → SC8-5b (subsequence `ψ`, uniform `Qup`); on `H ∘ ψ`: T4A-4 with `hdeep` instantiated at
`(Hext ∘ ψ).toHistory` ⇒ B13's `htraced`; SC4-b ⇒ `eps`-necks at `y (ψ (ψ' i))`; contradiction. PROVED, clean.

## Lead message (WATCH_SC8 cycle 2) — delta, recorded before proving the change
- The subsequence → full-sequence passage is done on THIS side: the ONE remaining hypothesis is now stated in
  SC8-4b's natural shape (`∃ σ, StrictMono σ ∧ ∀ᶠ i, <supply body at σ i>`, for every sequence `K t y R` with the
  B13-style `∀ n`/`∀ᶠ n` inputs and the separating-set data), and the new lemma
  `ObservedHistory.eventually_neck_supply_of_forall_subseq_neck_supply` (`TerminalHornBlowupContradiction.lean`) turns
  it into the `∀ᶠ n` form SC6-c′ consumes: `by_contra`, `Filter.not_eventually`, `Filter.extraction_of_frequently_atTop`
  to a bad `σ₀`, the hypothesis on `K ∘ σ₀` (all inputs transfer by `StrictMono.tendsto_atTop.eventually`), a common
  index. T4A-7 applies SC6-c′ to `Hext ∘ ψ` (SC8-5b's subsequence) with the supply converted there.
- Normalization kept: `Rₙ := Gₙ.flow.scalar τₙ xₙ` (the slice scalar at the base point, `hscal`), `Rl := R_L(xₙ)`
  only enters through `|Rₙ − Rlₙ| ≤ Rlₙ/2` (RescalingFactor); the rescaled base point has scalar `1` (X5d's input).

## Lead message (latest) — RISK on SC8-1's basepoint-scalar-1 clause: choice recorded
Option (a) is IN FORCE and has been since the first assembly draft: the blow-up factor is the slice scalar at the base
point, `Rₙ := (G n).flow.scalar (τ n) (x n).val` (Lemma C1 output `o4`/`o5` compares it to `R_L(xₙ)` only through
`|Rₙ − Rlₙ| ≤ Rlₙ/2` and `(sₙ − τₙ)·Rlₙ ≤ 1/(n+1)`), and Lemma A / the deep supply receive
`hscal : ∀ n, metricScalarAt (Hextₙ.stageMetric … extendAtTime) (y n) = R n` EXACTLY (proved on the `extendAt` side by
`riemannianEDistOf_extendAt_stageAt_eq`/`stageMetric_extendHorizon_last_of_mem_Icc`, i.e. the top-slice metric of `Hextₙ`
IS `Gₙ.flow.base.metric τₙ`). SC8-1 is called with this `hscal`, so its clause "rescaled basepoint scalar = 1" holds
exactly and `hnonflat` for SC5-1b is the equality form. `R_L(xₙ)` is never used as a normalization; it only supplies the
growth `Rₙ → ∞`, `Rₙ·τₙ → ∞` (via `Rₙ ≥ Rlₙ/2`, `τₙ ≥ a/2` for large `n`) and the `L`-side ball inputs (SC7, SC2-e,
SC4-c) which are transported to the slice `τₙ` by the factor-2 comparison `Rlₙ/2 ≤ Rₙ ≤ 3Rlₙ/2` inside C2.

## Cycle 3 (lead: NO conditional headline) — the deep supply is PROVED here, the leaf is unconditional

**T4A-8 = the per-layer deep neck supply** (`Surgery/Topology/TracedRegionDeepNeckSupply.lean`, ns `…ObservedHistory`):
- `exists_tolerance_subseq_neckAlternative_of_isTracedRegion_uniform : ∃ etaD > 0, ∀ {κ ε C1 C2 Cq qcan} {Ctime} {phi},
  0 < κ → 0 < ε → ε ≤ etaD → Admissible phi → ∀ (K : ℕ → ObservedHistory) t y R, (∀ n, 0 < R n) →
  hscal (basepoint scalar = R n EXACTLY) → Tendsto R → htop → hnc(r ≤ ε, v < t n) → hpinch(v ≤ t n) → (∀ n, qcan ≤ Cq·R n) →
  hwit(v ≤ t n) → hderiv(v < t n) → htopneck → ∀ S V W, hV → hW → hVW → hS(7/√R) → hpoints(7 < A) → ∀ T > 0,
  (∃ Kb ≥ 0, ∀ A T' ≤ T, ∀ᶠ n, traced (A/√R) (T'/R) (Kb·R)) → ∀ T', 0 ≤ T' → T' < T → ∀ A c > 0,
  ∃ σ, StrictMono σ ∧ ∀ᶠ i, <SC6-c supply body at depth T' along σ>`. Route exactly the lead's (i)–(vi):
  `etaD := min (1/1000) (neckModelTolerance (1/2000))`; (ii) SC8-1 `exists_window_pointed_flow_limit_of_isTracedRegion`
  on `(−T, 0]` (uniform premise instantiated at `T' = T`) ⇒ window limit `(P, F, ψ, Wo, φ, G, …)`; (iii) SC8-2 line at the
  basepoint; (iv) OPTION (c): `htopneck A := 1, c := 1/2` + `hwit` at the top slice ⇒ `SpatialNeck` at `y n` with tolerance
  `neckModelTolerance (1/2000)` (after `scaleMetric`/`.mono`), transported along `F.basepoint_map` and passed to the limit
  with `exists_spatialNeck_of_pointed_spatialNecks_on_compact_ball` (T4A-9) on the compact `(D+1)`-ball of the complete
  limit (`RiemannianMetricComplete.closedEBall_isCompact`) ⇒ a `(1/1000)`-neck at `P.basepoint`;
  `nkP.simplyConnectedSpace_of_line` (SC8-3) with `Ric ≥ 0` from the curvature-operator bound; (v) SC5-1b on
  `[−(T'+T)/2, 0] ⊂ (−T, 0]` with `hnonflat` = the EQUALITY basepoint scalar `1` (from `hscal`, SC8-1's clause) ⇒ the
  ℝ×S²-structure of every slice; (vi) SC8-4b `eventually_forall_neckAlternative_of_window_product_structure` along
  `f ∘ ψ`. PROVED, clean (0 errors, 0 warnings).
- `exists_tolerance_eventually_neckAlternative_of_isTracedRegion_uniform` (same premises, conclusion `∀ᶠ n in atTop,
  <supply body at n>`): `by_contra` + `Filter.not_eventually` + `Filter.extraction_of_frequently_atTop` ⇒ bad `σ₀`; the
  subsequence theorem on `K ∘ σ₀` (every `∀ n`/`∀ᶠ n` input transferred by `StrictMono.tendsto_atTop.eventually`) gives a
  further subsequence with the supply, a common index contradicts. PROVED, clean. This is the `hdeep` T4A-4 consumes;
  the converter of cycle 2 (`eventually_neck_supply_of_forall_subseq_neck_supply`) is superseded and removed.

**T4A-9 = pointed spatial necks pass to a compact-ball limit** (`Perelman/CanonicalNeighborhood/PointedSpatialNeckLimit.lean`):
`exists_spatialNeck_of_pointed_spatialNecks_on_compact_ball (ha : 0 < alpha) (hsmall : alpha < 1/32) : ∃ D > 0, ∀ X f L maps
C, canonical domains → ∀ x, 0 < R_L x → ∀ R > 0, IsCompact (closedBall_L x R) → D < √(R_L x)·R → (∀ᶠ n, Nonempty
(SpatialNeck (X (f n)).metric (neckModelTolerance alpha) (maps n x))) → Nonempty (SpatialNeck L.metric (2·alpha) x)` —
the compact-ball adaptation of `PointedSpatialNecks.lean` (the uniform image-radius `D`, quadratic control on the ball,
inverse comparison, `exists_transport_of_local_comparisons`). PROVED, clean.

**Deviation from the cycle-2 binder shapes (recorded)**: `hwit` is now demanded with `v ≤ t n` (top slice included) in
T4A-8 and in Lemma A, because option (c) reads the top-slice witnesses; the `extendAt` limit-inputs lemma (T4A-3) was
tightened accordingly (its conjunct (iii) is `(v : ℝ) ≤ extendAtTime`), and the `<`-shaped consumers (SC8-5b, SC4-b)
receive `hv.le`.

**T4A-7 (Lemma A) re-stated without `hdeep`**: `exists_tolerance_false_of_deep_horn_sequence` has NO supply binder any
more; `epsW := min epsW₀ etaD` (SC4-b's and T4A-8's tolerances), and T4A-8 is instantiated on `(Hext ∘ ψ).toHistory`
(SC8-5b's subsequence) with the transported class data; then T4A-4 ⇒ B13's `htraced` ⇒ SC4-b ⇒ contradiction.
PROVED, clean.

**The old Lemma C (one theorem from the horn presentations to `False`) timed out at the default heartbeat budget**; per
AGENTS (no `maxHeartbeats`) it is split at the natural boundary "slice selection in the `G(τ)`-world" / "blow-up on the
`extendAt` histories":
- **T4A-10 = C1** (`Surgery/Topology/TerminalHornSliceSelection.lean`): `exists_slices_of_deep_horn_presentation_sequence :
  ∃ eta etaC > 0, ∀ {κ ε ε₁ C1 C2 qcan εc a} {Ctime Cgrad} {phi}, hypotheses (class data, `a ≤ sₙ`, presentations `P n` with
  `εP n ≤ eta`, deep horn points `xₙ` with `(n+1)·max(Λ/r², max qcan 1) ≤ R_L(xₙ)`, no `εc`-neck) → ∃ τ Q S V W,
  (o1) `τₙ ∈ (tₙ, sₙ)` ∧ (o2) `1 ≤ Q m` ∧ (o3) no `min(εc/(1+εc), 1/12)`-neck of `G(τₙ)` at `xₙ` ∧ (o4) `|Rₙ − Rlₙ| ≤ Rlₙ/2`
  ∧ (o5) `(sₙ − τₙ)·Rlₙ ≤ 1/(n+1)` ∧ (o6–o8) `V W` open, disjoint ∧ (o9) `S ⊂ closedBall(7/√Rₙ)` ∧ (o10) `∀ m, ∀ᶠ n`,
  SC4-c's separation clause at radius `m+1` on the slice ∧ (o11) `∀ m, ∀ᶠ n`, `L`-bound with `Q m` on the open `8(m+1)`-ball,
  ball capture `ball_τ(16r/17) ⊂ val '' closedBall_L(r)`, scalar closeness `< Rlₙ` on `closedBall_L(r)` (`r = 3(m+1)/√Rl`)
  ∧ (o12) `∀ m, ∀ᶠ n`, SC2-e's neck-alternative witnesses on `closedBall_L(r)`. `eta := min eta₀ (min eta₇ eta₂)`,
  `etaC := min eta₂ eta₇` (SC4-c, SC7, SC2-e). Diagonal choice over `Fin (n+1)` with
  `Filter.exists_seq_mem_Ioo_forall_of_eventually_nhdsLT`; `hRs` from `a ≤ sₙ`.
- **T4A-11 = per-slice `extendAt` transports** (`Surgery/Topology/TerminalHornExtendAtTransports.lean`, one history):
  `extendAt_scalar_lower_on_ball_of_gradientBoundBefore`, `extendAt_scalar_upper_on_ball`,
  `extendAt_neck_alternative_on_ball`, `extendAt_exists_separating_sets`, `extendAt_not_nonempty_spatialNeck` — each is
  `extendAt_stageAt_iff` (T4A-2) with the appropriate predicate, fed by T4A-6.
- **T4A-12 = C2** (`Surgery/Topology/TerminalHornBlowupSequence.lean`): `exists_tolerance_false_of_deep_horn_slices :
  ∃ epsW > 0, ∀ …, C1's outputs (o1)–(o12) + `(n+1) ≤ R_L(xₙ)` + `a ≤ sₙ` → False`: `Rₙ := Gₙ.flow.scalar τₙ xₙ`
  (RescalingFactor from o4/o5), `τₙ ≥ a/2` eventually (from o5 and `Rlₙ ≥ n+1`) ⇒ `Rₙ·τₙ → ∞`; `y n` by
  `exists_heq_extendAt_stageAt`, `hscal` exact; `hradA : A/√Rₙ ≤ 16·(3(⌊A⌋₊+1)/√Rlₙ)/17`; hballLow/hballUp/htopneck/
  separation/no-neck by T4A-11; T4A-5 converts the integer-radius clause to radius `A`; Lemma A closes.
- **Leaf** (`Surgery/Contract/FineCutNeckSupplyStrongLeaf.lean`): `fineCutNeckSupplyStrong_holds P₀ g₀ :
  FineCutNeckSupplyStrong P₀ g₀` — UNCONDITIONAL. `ε₁ := 1/30000`, `eta` := C1's, `εcone := min etaC (min epsW
  crossingNeckAccuracy)`; `by_contra`; per `n` a bad tuple at `Kfine := n+1` (`hbad`), `choose`; pinching and `a ≤ sₙ`
  from T4A-1; C1 then C2.

## Final status (2026-09-26, T4′ closed on this lane)

All lane files check clean with `-Dweak.linter.mathlibStandardSet=true` (0 errors, 0 warnings, no `sorry`/`axiom`/
`nolint`/`maxHeartbeats`, no comments) against the scratch oleans (`t4a/olean/SC8`, uncommitted suppliers rewritten to
`SC8.*`), in this dependency order (13 new files, 2317 lines):
1. `Geometry/Metric/Distance/SeparatedSideBallClause.lean` (41)
2. `Surgery/Topology/HistoryPinchingOfCutoffRecords.lean` (47)
3. `Surgery/Topology/RetainedCoreHistoryExtendAtStageTransfer.lean` (62)
4. `Surgery/Topology/RetainedCoreHistoryExtendAtLimitInputs.lean` (105)
5. `Surgery/Topology/HistoryStrongNeckStaggeredDepthInduction.lean` (214)
6. `Surgery/Topology/HornPointSliceGeometry.lean` (120)
7. `Perelman/CanonicalNeighborhood/PointedSpatialNeckLimit.lean` (116)
8. `Surgery/Topology/TracedRegionDeepNeckSupply.lean` (286)
9. `Surgery/Topology/TerminalHornBlowupContradiction.lean` (318)
10. `Surgery/Topology/TerminalHornSliceSelection.lean` (432)
11. `Surgery/Topology/TerminalHornExtendAtTransports.lean` (189)
12. `Surgery/Topology/TerminalHornBlowupSequence.lean` (286)
13. `Surgery/Contract/FineCutNeckSupplyStrongLeaf.lean` (101)

Axiom closures (scratch `#print axioms` probe, run against the emitted oleans and then deleted):
`fineCutNeckSupplyStrong_holds`, `exists_tolerance_false_of_deep_horn_slices`,
`exists_slices_of_deep_horn_presentation_sequence`, `exists_tolerance_false_of_deep_horn_sequence`,
`ObservedHistory.exists_tolerance_eventually_neckAlternative_of_isTracedRegion_uniform`,
`ObservedHistory.exists_tolerance_subseq_neckAlternative_of_isTracedRegion_uniform`,
`exists_isTracedRegion_of_forall_neckAlternative_of_staggered_supply`,
`FiniteHorn.exists_spatialNeck_of_pointed_spatialNecks_on_compact_ball` — each exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Uncommitted suppliers imported directly (accept before this lane): SC8's `TracedRegionWindowLimit` (SC8-1),
`ScaledPointedLimitLine` (SC8-2), `Geometry/Neck/LineNeckSimplyConnected` (SC8-3), `TracedRegionWindowProductNeck`
(SC8-4b), `HistoryStrongNeckTopSliceTracedRegion` (SC8-5a), `TracedRegionTimeZeroUniformBound` (SC8-5b). Everything
else imported is committed at HEAD 5186a2b7c.

Skeleton edit (NOT applied here; `PoincareEndgame.lean` is untouched): add
`import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FineCutNeckSupplyStrongLeaf` and, per SL2's
design, replace the `sorry` of the fine-cut leaf by
```lean
theorem fineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupplyStrong P₀ g₀ :=
  fineCutNeckSupplyStrong_holds P₀ g₀
```
Root aggregate: the 13 new modules need registration in `DifferentialGeometry.lean` (not done by this lane).
Deferred merges (recorded, not done): SC6-c becomes a corollary of the staggered induction; the old converter of cycle 2
was removed with the unconditional Lemma A.
