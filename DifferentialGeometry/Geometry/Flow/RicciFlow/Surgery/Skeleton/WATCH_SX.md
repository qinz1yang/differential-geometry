# WATCH_SX — advisory watcher notes for lane SX (read-only reviewer)

## Cycle 1 (2026-09-26 ~16:25 local)
State read: log (items 1–2 DONE, 3 in progress, 4 not started); `AncientLimitSurvivorCanonicalWitness.lean` (463),
`CrossingAncientLimitSpatial.lean` (299), `SpatialCrossingContinuationLeaf.lean` (428, full proof text present).

Checks passed:
- `spatialCrossingContinuation_holds (P₀) (g₀) : SpatialCrossingContinuation P₀ g₀` — exact target; both `def` files
  are committed and unmodified (mtimes 11:54 / 13:32, `git status` clean for them).
- H16: no age shortcut (per-`n` `θcapₙ = 1 − 1/(n+2)`, the `¬CapWindowPoint` goes into X3/X4 as in X7); tracing
  across all events via the extended history `extendAt` + `isTracedRegion` (B13 machinery); `whole` via
  `pushforwardOfInjective` along `Subtype.val`; capture exact in the scaled ball (`2C+1 < k+3`, `W k n = ball(k+3)`),
  pulled back by `scaleMetric R⁻¹` — radii in original units. `εbar ≤ coneAccuracy`, `0 < ε`, `∃ Cx` before `∀ B`. OK.
- All cited suppliers exist with matching names (grep): X3 `exists_subseq_depthExtendable_pos`
  (CrossingTimeZeroBound), `exists_subseq_windowAnchorBound_of_depthExtendable` (CrossingWindowAnchorBound),
  `depthExtendable_add_of_windowAnchorBound` (CrossingDepthExtension), `exists_spatialCanonicalWitness_extendAt_of_before`,
  `volume_ge_extendAt_of_terminalNoncollapsedBefore`, `curvatureOperatorLowerBoundAt_extendAt_of_pinched`
  (RetainedCoreHistoryExtendAtBefore), `derivativeBoundBefore_of_derivativeBoundOn` (SpatialCanonicalContinuationCases),
  `crossingNeckAccuracy`, `crossingWindowNeckAccuracy`. No `sorry`, no heartbeat options in the three files.

Findings:
- [RISK] Supplier files NOT committed: `CrossingWindowAnchorBound.lean`, `CrossingMaximalWindow.lean` (X7 lane,
  `??`). The SX acceptance must build/commit them together (or after) X7's acceptance.
- [NIT] `AncientLimitSurvivorCanonicalWitness.lean:327–330`: four stacked `omit [SigmaCompactSpace M] in` before
  `metricDistance_le_image`; keep one.
- [NIT] Private copies to record for the deferred merge (already logged): `derivativeBoundBefore_double`
  (= `CrossingTracedRegion.lean:29`), `domain_subset_of_ball_subset` / `metricDistance_le_image`
  (= `SpatialCanonicalWitnessTransport.lean:895–928`), X1 bad-point copy, X5 prefix copy.
- [RISK, strong SX, item 4] No existing lemma transports `HistoryStrongNeck` along `prefixAt`
  (grep `historyStrongNeck.*prefixAt` = none; only `historyStrongNeck_extendHorizon_iff`,
  `HistoryStrongNeckExtendHorizon.lean:83`, exists and `extendAt` IS `extendHorizon … (G.closedPrefix …)`,
  `RetainedCoreHistoryExtendAt.lean:24`). The event branch works on `H.prefixAt j.castSucc`, so the final HSN must
  land on `H.toHistory` at `j.castSucc`. Suggestion: build the HSN DIRECTLY on the original `H` (not on `K n` /
  prefix): for `x ∈ W k n` turn the block's maps `f j` + `RegularCrossing` + `f last x = x` into a
  `BackwardPointTrace` of the extended/prefix history, then to `H` with `backwardPointTraceOfPrefix`
  (`RetainedCoreHistoryPrefix.lean:38`) and the field-copy `⟨A.point, A.endpoint_eq, A.crossing⟩` used in
  `backwardSurvivorDomain_extendHorizon` (`HistoryStrongNeckExtendHorizon.lean:95`). Then
  `W k n ⊆ H.backwardSurvivorDomain first k` by `subset_backwardSurvivorDomain_iff` (`HistorySurvivorDomain.lean:209`)
  and `backwardSurvivorMap = f j` on `W k n` by `backwardSurvivorMap_eq_point` (`HistorySurvivorDomain.lean:81`).
- [BLOCKER-in-waiting, strong SX neck splicing — read BEFORE starting item 4] The comparison inside
  `StrongNeck`/`TruncatedNeck` is `MetricComparisonOn` whose `pullback_eq` and `jet_zero` quantify over ALL
  times `s : ℝ` (`FiniteHornGeometry.lean:51–56`); every exact transport in the tree (`TruncatedNeck.restrictOpen`
  `TruncatedNeck.lean:62`, `StrongNeck.restrictOpen` `StrongNeckRestriction.lean:21`, `MetricComparisonOn.mapIsometry`
  `SpatialCanonicalWitnessTransport.lean:436`) therefore needs the two metric families EQUAL FOR ALL τ. B13's `h k n`
  equals the survivor pull-back only on `[−(k+2), 0]` (block clauses) and is unconstrained elsewhere, while any
  HSN `gflow` is pinned on all of `[time first, s)`. So "identify `h k n` with `gflow` on `[−1/5,0]`, then transport"
  does NOT typecheck without a window-congruence lemma for `MetricComparisonOn`, and that lemma needs a global
  `Tensor0SField` pull-back of the new metric at off-window times (not available; would need a cut-off and a strictly
  smaller cylinder).
  Suggested route (no window congruence): do NOT feed B8-young with B13's `h`; feed it `h'` built from the spliced
  survivor-domain flow, so all later equalities hold for every τ by construction:
  1. `first := activeStage a` (the block's `a = t − 2(k+2)/R`, so `time first ≤ a ≤ t − 1/(5R)`), `U :=
     H.backwardSurvivorDomain first k`; `W k n ⊆ U` via the trace argument above.
  2. `gflow` on `U`: if `first = k`, `gflow τ := (G.flow.base.metric τ).restrictOpen U` (as
     `historyStrongNeck_of_strongNeck`, `HistoryStrongNeck.lean:60`); else splice `exists_backwardSurvivor_isSolutionOn
     first k` (`HistorySurvivorFlow.lean:180`) with `G.restrictOpen U` at `c := time k` by
     `metricCLMSection_jointContMDiffOn_ite_of_ricciFlow` / `isSolutionOn_ite_of_ricciFlow` (`Solution/Seam.lean:103`),
     copying the template `HistorySurvivorIncoming.lean:226–280` (there with the terminal limit; here use
     `G.closedPrefix b'` for each `b' < s`). HSN needs IsSolutionOn on `closedOpen (time first) s`: get it from
     `isSolutionOn_of_joint_metric` (`Solution/JointRegularity.lean:19`) with joint smoothness on `Ico × univ`
     assembled locally from the closed pieces `[time first, b']` (small new generic lemma; no closedOpen seam lemma
     exists in the tree — grep).
  3. `h' k n σ := scaleMetric R ((gflow (t + σ/R)).restrictOpen W')` with `W'` = `W k n` as an `Opens U`. Check
     B8-young's three `h`-hypotheses — all are window-local: `IsSolutionOn` on `closed (−(k+2)) 0` (time-rescale +
     restrict of `gflow`), the current-slab identity (gflow = G there), and `hconv` (only `s ∈ Icc (−(k+1)) 0`,
     rewrite `h' = h` there from the block's last clause + `backwardSurvivorMap = f j` +
     the metric-level form of SC3's rewrite chain `HistoryStrongNeckTrace.lean:50–64`
     (`backwardSurvivorSlabMetric`, `metricScalarAt_localPull` → drop the scalar wrapper,
     `extendedMetric_before`, `backwardSurvivorTerminalMap_val`, `stageMetric_castSucc_apply`)).
  4. K's neck `data.strong : StrongNeck {h'} ε ⟨y,hy⟩ 0` → `StrongNeck.ofParabolic` (`NeckParabolicTransport.lean:71`,
     after `timeRestrict` `CanonicalWitnessTimeRestrict.lean:19` to match domains) → push from `W'` to `U` (new
     `StrongNeck.ofRestrictOpen`, the converse of `StrongNeck.restrictOpen`, one-liner via `mapIsometry` with
     `openSubtypePartialDiffeomorph`, pattern `SpatialNeck.ofRestrictOpen`, `SpatialNeckOpenSubset.lean:19`; `hiso`
     holds ∀ s by `restrictOpen_inner`) → `TruncatedNeck.ofStrongNeck` depth `1/5` with jets from `IsSolutionOn gflow`
     (`StrongNeck.comparison_jet_differentiableWithinAt_of_lt_one`, as `HistoryStrongNeck.lean:57–59`) → `.mono` to ε₁.
  This keeps H20 (b)–(d): K produced on the common flow, exact, `α := ε`, no approximate transport.

## Cycle 2 (16:36)
- Stacked `omit` NIT resolved (one `omit` left). Leaf touched at 16:27 (small edit), no `sorry`/heartbeat options;
  log unchanged since 16:11; strong leaf not started. No new findings.

## Cycle 3 (16:47)
- SX leaf DONE per log (axioms clean). Statement re-checked: exact `SpatialCrossingContinuation P₀ g₀`; no drift.
- Strong-SX route adopted. New bricks read:
  - `HistoryStrongNeckSurvivorSlab.lean` (brick A, `exists_backwardSurvivor_incomingSlab_flow`): statement fields
    match `HistoryStrongNeck` exactly (slab identities on `Icc`, `Ico (time k) s` restriction, IsSolutionOn on
    `closedOpen (time first) s`); `first = k` / `first < k` split; seam via `Seam.lean`; `isSolutionOn_of_joint_metric`
    only needs the equation on `D.regular`, so the `Ioo` use is right. Looks sound. OK.
  - `StrongNeckPullbackTransport.lean` (brick D): `ofMetricEq` (∀τ equality + window ⊆ D'), `ofLocalPullback`
    (injective local diffeo, exact `mapIsometry`, all-τ `hiso`). Sound; names unique (grep). OK.
  - [NIT] `StrongNeck.castTime` is just `h ▸ nk`; drop it unless used ≥ 2 times.
- [RISK, reminder for X5s′] B8-young's `hid` compares `h'` with `(stageMetric …).restrictOpen (W k n)` on the
  current slab: with `h'` defined via `gflow` on `U` then pulled to `W k n`, you need
  `localPull ((G τ).restrictOpen U) (W k n ↪ U) = (G τ).restrictOpen (W k n)` — prove once as an `ext_inner`
  lemma (both sides are `G τ` at `x.val` with `mfderiv_subtype_val`), and reuse it for `hconv` on the window.

## Cycle 4 (16:58)
- `SurvivorBlockStrongNeck.lean` (259 lines, bricks B+C) read. Math is right: traces built from the block's `f`,
  `RegularCrossing`, `f top = val` (`BackwardPointTrace` literal), `backwardSurvivorMap = f` by
  `backwardSurvivorMap_eq_point`, `h σ = scale R (localPull (gflow (t+σ/R)) ι)` on `[−(k+2),0]` via
  `extendedMetric_before` / `stageMetric_castSucc_apply` (SC3 chain at metric level); the neck packaging goes
  `ofMetricEq` (∀τ, by `hfam_def`) → `ofParabolic` → `ofLocalPullback` → `TruncatedNeck.ofStrongNeck` (jets from
  `hsol`, regular window `Ioo (t − R⁻¹) t` inside `Ioo (time first) s` since `time first ≤ t − 2(k+2)/R`) → `mono`.
  HSN fields all supplied exactly; `time first ≤ t − (1/5)R⁻¹` checked. No sorry/options. OK.
- [NIT] Public names `exists_survivor_flow_of_block` ("block" = lane jargon for B13's output). Suggest
  `exists_backwardSurvivor_flow_localPull_eq_of_backwardTraces` or similar describing the conclusion (NAMING.md).
- [RISK, X5s′/L′] X5s′ concludes HSN on `(K n).toHistory` at `activeStage τ` with a slab `Gn` whose type depends on
  `activeStage τ`; carrying it to `H.toHistory.HistoryStrongNeck (Fin.last _) G` needs the `generalize … = k at hlast;
  subst` pattern (as the SX leaf's `metricScalarAt_extendAt_eq`, lines 119–150) BEFORE `historyStrongNeck_extendHorizon_iff`.
  Consider stating X5s′'s `Gn` hypothesis on `Fin.last` of an `extendAt` history directly, or supply `Gn` as
  `hlast ▸ G` and prove the cast lemma once (HSN is a Prop, so `HEq`-free `subst` works after generalizing).

## Cycle 5 (17:10)
- `CrossingAncientLimitStrong.lean` (X5s′, 301 lines) read. Statement = X5s's binders + `ε ≤ ε₁ < 1/11` + per-`n`
  slab `Gs n` of the ACTIVE stage (`t n < s n`, equal to the stage metric on `[time k, t]`); conclusion: witness with
  cap-tube ∧ (neck ⇒ `(H n).HistoryStrongNeck (activeStage t) (Gs n) ε₁ y t`). Matches H20 (b)–(d): K from B8-young
  on `h'` = survivor-domain flow (for `n ≥ N k`, `h` otherwise — only eventual hypotheses, fine), `α := ε`, exact
  transports only, label kept through the conversion lemma. B8-young's `hsolh`/`hid`/`hconv` discharged by window
  equality `hh'eq` + `IsSolutionOn.congr_metric` (exists, `Solution/Congruence.lean:13`). No sorry. OK.
- Remaining: (P) prefixAt transport and the strong leaf; the cast RISK of cycle 4 applies when supplying `Gs n` from
  `K n = extendAt …` (stage index `activeStage τ` vs `Fin.last`).

## Cycle 6 (17:20)
- Brick (P) `HistoryStrongNeckPrefix.lean` (134 lines): `historyStrongNeck_of_prefixAt` statement is the needed
  direction (prefix ⇒ `H` at `k`), proof by field transfer with `first` re-indexed by `Fin.castLE` and the traces
  moved back with `backwardPointTraceToPrefix`. Sound. OK.
- [NIT] private `neckBody` / `historyStrongNeck_iff_exists_neckBody` duplicate the private `strongNeckBody` /
  `historyStrongNeck_iff_exists_strongNeckBody` of `HistoryStrongNeckExtendHorizon.lean:19–46`; list as a deferred
  merge (promote one public `HistoryStrongNeck` body characterization).

## Cycle 7 (17:30)
- `StrongSpatialCrossingContinuationLeaf.lean` (496 lines) present with a full proof text: target
  `strongSpatialCrossingContinuation_holds (P₀) (g₀) : StrongSpatialCrossingContinuation P₀ g₀` — exact.
  `εbar := min ε₁ (min coneAccuracy …)` gives `εbar ≤ coneAccuracy ∧ εbar ≤ ε₁`; `Cx := C` from X5s′ (independent of
  `B`). The cast `activeStage τ = Fin.last` is handled by `generalize … ; subst` in `slab_metric_of_extendAt` /
  `strong_clause_of_extendAt`, then `historyStrongNeck_extendHorizon_iff` (terminal) — cycle-4 RISK closed. OK.
- [RISK → cleanup, do before acceptance] Clone: the strong leaf re-declares the four private helpers of the SX leaf
  (`derivativeBoundBefore_double`, `exists_spatial_crossing_bad_point`, `le_static_scale_of_neckRadius_le`,
  `metricScalarAt_extendAt_eq`) and repeats its whole contradiction skeleton. Since
  `spatialCrossingContinuation_of_strongSpatialCrossingContinuation` already exists
  (`StrongSpatialCrossingContinuation.lean`, after the def), once the strong leaf compiles the SX leaf should be
  reduced to `spatialCrossingContinuation_holds P₀ g₀ := spatialCrossingContinuation_of_strongSpatialCrossingContinuation
  P₀ g₀ (strongSpatialCrossingContinuation_holds P₀ g₀)` (or dropped, with C4 consuming the strong one), deleting ~400
  duplicate lines. Then `CrossingAncientLimitSpatial.lean`'s corollary (non-strong X5s) may also become unused —
  keep only if another consumer needs it (AGENTS: no clones; zero consumers ≠ dead, but a strictly weaker duplicate
  proof of the same conclusion is).

## Cycle 8 (17:40)
- Log: STRONG SX DONE (compiles clean, per lane); final verification/axiom section still pending. Cycle-7 clone
  RISK still open (both leaves carry the same four privates + skeleton; the log lists it as a deferred merge, but the
  cheaper fix is deriving SX from strong SX via the existing `spatialCrossingContinuation_of_strongSpatialCrossingContinuation`).
- [NIT] `StrongNeck.castTime` has one use; inline `h ▸` or keep — reviewer's call.
