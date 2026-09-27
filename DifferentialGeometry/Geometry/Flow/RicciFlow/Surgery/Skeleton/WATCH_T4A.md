# WATCH T4A — advisory watcher findings (read-only reviewer)

## Cycle 1 (2026-09-26, ~16:25 local)

Files read: OPUS_FILL_LOG_T4A.md (through "Statements"), the 7 lane files, SC8 log tail, SC8-1/4b/5a/5b
statements, SC6's `isTracedRegion_of_forall_neckAlternative`, `TracedRegionLineNeck`, `LineProductSplitting`.
Lane files: no `sorry`/`admit`/`axiom`/`set_option` other than `autoImplicit`/`nolint`/comments/diagnostics.

VERIFIED (no action):
- Staggered induction `exists_isTracedRegion_of_forall_neckAlternative_of_staggered_supply`
  (HistoryStrongNeckStaggeredDepthInduction.lean:16) is NOT circular: traced depth `δ + mδ/2` (ih) with the
  uniform constant `K = 8√3(1+φ1+φ0)Qup` → `hdeep` supply at the strictly smaller depth `δ/2 + mδ/2` → SC6
  single step → traced depth `δ + (m+1)δ/2`; `δ = (10·Qup)⁻¹` is uniform (one `Qup` for all radii), gain
  `δ/2` per step, `K` independent of depth, so `hdeep`'s uniform-`K` premise is honestly produced.
- `Qup` chain is not circular: SC8-5a (per-radius Qup(A), top slice only) → SC8-5b (uniform `C₀` on a
  subsequence ψ) → staggered induction run on `H ∘ ψ` (TerminalHornBlowupContradiction.lean ~l.265–330).
- No age hypothesis on deep horn points (H12/F4): only `R n * τ n → ∞` (absolute time) is assumed.
- Pinching phi depends only on (P₀, g₀) (HistoryPinchingOfCutoffRecords.lean:16) — compatible with `Kfine`
  independent of p₀/H.

FINDINGS:
- [RISK] Stale supplier survey in the log. The log says SC8-4a/4b and SC8-3 "have NOT landed"; on disk they
  have: SC8-4a `Perelman/CanonicalNeighborhood/LocalPullProductNeck.lean`, SC8-4b
  `eventually_forall_neckAlternative_of_window_product_structure` (Surgery/Topology/TracedRegionWindowProductNeck.lean:248,
  no sorry), SC8-3 `SpatialNeck.simplyConnectedSpace_of_line` (Geometry/Neck/LineNeckSimplyConnected.lean:42).
  Re-survey and plan the `hdeep` discharge against the delivered shapes.
- [BLOCKER until discharged] `exists_tolerance_false_of_deep_horn_sequence` (TerminalHornBlowupContradiction.lean:22)
  takes the deep supply as a universally quantified hypothesis (the `∀ (K : ℕ → ObservedHistory) t y R … ∀ T,
  (∃ Kb, …) → ∀ T' < T, … neck` binder, ~l.120–175). Acceptable only as an internal factorization; the leaf
  must discharge it (no conditional deliveries). Concrete route, per bad (T, T', A, c):
  (i) by contradiction, `Filter.not_eventually` + `Filter.extraction_of_frequently_atTop` → bad subsequence σ;
  (ii) SC8-1 `exists_window_pointed_flow_limit_of_isTracedRegion` (TracedRegionWindowLimit.lean:82) at depth
  `T` with `K := Kb` (instantiate the premise at `T' := T`) along `K ∘ σ` — this is the "window limit at depth
  T from traced regions at depth T" required by the design; (iii) SC8-2 `exists_line_of_scaled_pointed_limit_of_separating_set`
  (line at time 0); (iv) SC8-3 for `SimplyConnectedSpace P.M` — needs an ε-neck of `P.metric` at some point,
  the one interface SC8's log left open (threshold `4·max q 1 < R(x)` in B9w
  `neck_alternatives_of_local_flow_limit_on_window` at s = 0; the basepoint has R = 1, so rescale or pick a
  point with scalar > 4·max q 1); (v) `exists_surface_product_on_closed_interval_of_line`
  (DimensionThree/LineProductSplitting.lean:83) on `[-T', 0] ⊂ (-T, 0]` with `hR` (cone) from SC8-1's
  pinching clause on every layer, `hcomplete` at 0, `hbound` from SC8-1's curvature bound, `hnonflat` from
  R(basepoint)=1 — this gives `hprod` for all `s ∈ Icc (-T') 0` (product on the WHOLE window, not only time 0);
  (vi) SC8-4b along `f ∘ ψ` contradicts badness along σ. SC8-4b also needs `∀ s ∈ Ioc (-T) 0,
  RiemannianMetricComplete (G s)` — completeness per layer, from SC8-1 (check it is a delivered clause; if SC8-1
  only gives completeness at 0, that is a gap to raise).
- [RISK] Tolerance bookkeeping for the leaf: SC8-4b requires `ε ≤ 1/1000`, `TerminalHornBlowupContradiction`
  requires `ε ≤ epsW` and `ε ≤ crossingNeckAccuracy`, the staggered/SC6 step requires `ε₁ ≤ 1/30000`. Set
  `ε₁ := 1/30000` (satisfies `< 1/11`) and `εcone := min (min epsW crossingNeckAccuracy.{u}) (1/1000)`, with
  `epsW` obtained BEFORE the `∀ κ …` binders (it is: `∃ epsW` is outermost in both suppliers). `eta` must be
  `min` of SC2's, T1's and SC7's etas, chosen before `∀ κ`.
- [NIT] `TerminalHornBlowupContradiction` needs `Tendsto (R n * τ n)`: the slice `τ n` must be chosen with a
  uniform lower bound (e.g. `τ n ≥ a/2` from `exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords`, a ≤ s n);
  make sure the slice choice (SC7-3b/Finding 6) keeps `τ n ≥ s n - (something → 0)` so this holds.
- [update, cycle 1] SC8-1's conclusion DOES deliver per-layer completeness (`∀ s ∈ Ioc (-T) 0,
  RiemannianMetricComplete (G s)`), the cone clause, `curvDerivNormSq 0 (G s) ≤ K^2` (→ `hbound` of the
  splitting lemma) and `IsSolutionOn` on `openClosed (-T) 0` — so step (v) has all its inputs; the
  completeness gap above is closed.
- [NIT] `exists_surface_product_on_closed_interval_of_line` needs `a < b`; for `T' = 0` (allowed by `hdeep`)
  split on `[-(T'+T)/2, 0]` (or `[-T/2,0]`) and restrict `hprod` to `Icc (-T') 0`.

## Cycles 2–3 (16:31, 16:42)

New: log entries T4A-1..T4A-7 (all "PROVED, clean"), new file `Surgery/Topology/TerminalHornBlowupSequence.lean`
(`exists_tolerances_false_of_deep_horn_presentation_sequence`, l.28). Formatting-only diff in
TerminalHornBlowupContradiction.lean. `TracedRegionWindowLimit.lean` (SC8-1, uncommitted) was touched at 16:41 —
not by T4A per the logs; its completeness/cone/curvature clauses (l.~180–190) are unchanged in shape.

- [BLOCKER] The log (T4A-4, last paragraph) calls `hdeep` "the ONE remaining hypothesis of the leaf" and says
  the full-sequence passage from SC8-4b's subsequence form "is SC8-4b's side". The new
  `exists_tolerances_false_of_deep_horn_presentation_sequence` (TerminalHornBlowupSequence.lean:28) threads it
  further up as `∀ {etaD}, (∀ … K t y R …, supply) → …`. The leaf `fineCutNeckSupplyStrong_holds :
  FineCutNeckSupplyStrong P₀ g₀` cannot carry it (the def has no such binder), and a theorem
  `hdeep → FineCutNeckSupplyStrong P₀ g₀` is a conditional delivery (owner rule 2026-09-26: prove the full
  statement in one lane, build missing suppliers in the same lane). T4A must itself prove, as a standalone
  lemma (suggested name `ObservedHistory.eventually_forall_neckAlternative_of_isTracedRegion_uniform`, new file
  `Surgery/Topology/TracedRegionDeepNeckSupply.lean`), exactly the `hdeep` binder of
  TerminalHornBlowupContradiction.lean (~l.120–175) with `ε ≤ 1/1000` (+ whatever the product route needs) as its
  tolerance, by the route in cycle 1 (i)–(vi); then instantiate `etaD := that tolerance` in the leaf.
- [RISK] SC8-3 input (neck of the time-0 limit `P.metric`) is not free from `hdeep`'s premises. B9w's
  threshold `4·max q 1 < R(x)` (q = lim qcan/Rₙ ≤ Cq) may exceed every scalar of the normalized limit
  (R(basepoint) = 1, sup R ≤ Qup = SC8-5b's C₀, no relation to 4·Cq), so "a point above 4" is not guaranteed.
  Options, in order of cost: (a) avoid simple connectivity: use
  `exists_universalCover_surface_product_on_closed_interval_of_line` (DimensionThree/LineProductSplitting.lean:125)
  and prove a covering variant of SC8-4b's `hkey` (TracedRegionWindowProductNeck.lean:~538) — the capture there is
  local on a closed `r`-ball, so it needs the covering to be injective on that ball (true if `r` < half the
  length of the shortest non-contractible loop; NOT automatic — check); (b) get `SimplyConnectedSpace P.M`
  from the splitting of `P` itself (Cheeger–Gromoll, as in SC8-3's own proof) plus classification of the
  2-dimensional factor (nonflat, K ≥ 0: S², ℝ², or RP² excluded by orientability) — needs library that may not
  exist; (c) feed a genuine neck: the witnesses `hwit` at `yₙ` (scalar `Rₙ > qcan` eventually) have
  `capTubeHasNeckChart ε`; if the top-slice supply `htopneck` (which IS available to the caller, SC2-b) is added
  to the `hdeep` binder's premises, its neck at `yₙ` passes to the limit at the basepoint with threshold at scale
  `c = 1`, no `4·max q 1` issue — this is the cheapest and does not weaken anything since the caller has
  `htopneck` (TerminalHornBlowupContradiction.lean passes it to T4A-4 already). Recommend (c): add `htopneck`
  (and, if needed, `hball`) to the premises of the `hdeep` binder / the new supply lemma.
- [NIT] T4A-4 docs in the log say the base case "is the singleton, SC8-5a's device": fine; the base needs no
  `hdeep`, confirmed at HistoryStrongNeckStaggeredDepthInduction.lean (htop0 / `claim` zero case).

## Cycle 4 (16:53)

New: `Surgery/Contract/FineCutNeckSupplyStrongLeaf.lean` (144 l.) with
`fineCutNeckSupplyStrong_of_deep_layer_neck_supply (P₀ g₀) (hdeep : ∃ etaD > 0, ∀ … K t y R … ∃ σ, StrictMono σ ∧ ∀ᶠ i, supply) :
FineCutNeckSupplyStrong P₀ g₀`; `TerminalHornBlowupContradiction.lean` rewritten (520 l.) with the bridge
`ObservedHistory.eventually_neck_supply_of_forall_subseq_neck_supply` (l.22, extraction at l.150); `TerminalHornBlowupSequence.lean`
774 l.; `LocalFlowLimitBaseScalar.lean`, `StrongNeckPullbackTransport.lean` new. No `sorry`/overrides/comments found.

VERIFIED:
- Leaf conclusion is exactly the def: `ε₁ := 1/30000` (< 1/11, ≤ 1/30000), `eta := min eta₀ (min eta₇ eta₂)`
  (T1/SC4-tolerances, SC7, SC2; TerminalHornBlowupSequence.lean:143), `εcone := min etaC etaD` with
  `etaC = min (min eta₂ eta₇) (min epsW crossingNeckAccuracy)`, neck accuracy `min (εc/(1+εc)) (1/12)` (l.159);
  `Kfine := n+1` chosen by contradiction after `εc`, before `p₀` — independent of `p₀`, δ, ρ, `H`. Quantifier
  order is the def's. `InFixedHamiltonIveyRegion` and the event gradient binder are unused (`_`), as the log
  announced (Finding 3) — harmless (def-typed goal, no `unusedArguments`).
- The subsequence→full-sequence bridge is on T4A's side now (lead delta); the extraction is honest (bad σ₀,
  hypothesis on `K ∘ σ₀`, common index).

FINDINGS:
- [BLOCKER — lead decision needed] The leaf is CONDITIONAL: `fineCutNeckSupplyStrong_of_deep_layer_neck_supply`
  takes the SC8-4b-shaped deep supply as `hdeep`. The target `fineCutNeckSupplyStrong_holds : FineCutNeckSupplyStrong P₀ g₀`
  does not exist yet. Per the log this is the lead's chosen shape ("the ONE remaining hypothesis"), so: either T4A
  (owner's no-conditional-deliveries rule) or a named lane must prove
  `∃ etaD > 0, <that binder>` outright; route = cycle-1 (ii)–(vi): SC8-1 at depth `T` with `Kb` → SC8-2 line →
  splitting on `[-T', 0]` (`exists_surface_product_on_closed_interval_of_line`, LineProductSplitting.lean:83;
  `a < b` fix for `T' = 0`) → SC8-4b (`etaD := 1/1000`, SC8-4b's `ε ≤ 1/1000`). Please make sure some lane owns it
  before the S leaf is declared closed.
- [RISK — act NOW, before the binder shape freezes] The `hdeep` binder's premises (Leaf l.20–100; identical
  copies in TerminalHornBlowupSequence.lean ~l.30–95 and TerminalHornBlowupContradiction.lean ~l.22–75, ~l.200–290)
  contain no neck information at the time-0 slice, only `hwit` (existence of SOME witness with
  `capTubeHasNeckChart`, which may be a cap). Its discharge needs `[SimplyConnectedSpace P.M]` for the
  splitting lemma, i.e. SC8-3's input "an ε-neck of `P.metric`", whose only planned source (B9w at s = 0) has
  the threshold `4·max q 1 < R(x)` with `q ≤ Cq` possibly above every limit scalar (R(basepoint) = 1). As stated the
  binder is still TRUE (the time-0 limit splits `N × ℝ` by Cheeger–Gromoll; `N` a complete nonflat orientable
  surface with K ≥ 0 is S² or ℝ², so simply connected) but that classification is not in the library. Cheap fix:
  add the top-slice supply as a premise of the binder, in exactly `htopneck`'s shape
  (`∀ A c, 0<A → 0<c → ∀ᶠ n, ∀ x ∈ ball(yₙ, A/√Rₙ), c·Rₙ ≤ R(x) → ∀ W, W.capTubeHasNeckChart ε → ∃ nk, W.alternative = neck nk`
  at the top slice of `K n`). The callers already hold it (TerminalHornBlowupContradiction passes `htopneck` to
  T4A-4); with `hwit` at `yₙ` it gives a genuine ε-neck at `yₙ`, which passes to the limit basepoint (smooth
  convergence; nearest existing tool `exists_spatialNeck_of_pointed_strongNecks_on_compact_ball`,
  Perelman/CanonicalNeighborhood/PointedSpatialNecks.lean:24, is for `StrongNeck` in a `FlowSequence` — a spatial
  analogue may be needed) → SC8-3. Adding a premise only weakens the hypothesis; nothing else changes.

## Cycle 5 (17:04)

Log unchanged; leaf unchanged. New on disk (no log claims it yet): `Perelman/CanonicalNeighborhood/PointedSpatialNeckLimit.lean`
`exists_spatialNeck_of_pointed_spatialNecks_on_compact_ball` (l.26) — the spatial analogue named in cycle 4; it is
exactly the tool for the cycle-4 RISK fix (neck at `yₙ` from `htopneck` + `hwit` ⇒ neck of the limit at the
basepoint, `2α` accuracy, needs `D < √R(x)·R` with a compact ball: R(basepoint) = 1, so any radius `R > D` on the
complete limit works). `TerminalHornBlowupSequence.lean` (16:55) and `RetainedCoreHistoryExtendAtLimitInputs.lean`
(17:02, T4A-3's file, statement name unchanged) were re-touched.
- [RISK, carried] cycle-4 items unchanged: leaf still conditional on `hdeep`; binder still lacks the top-slice
  neck premise. If `PointedSpatialNeckLimit` is T4A's, it signals the discharge is under way in-lane — good; add the
  `htopneck`-shaped premise to the binder so the discharge can use it.

## Cycle 6 (17:15)

New: `Surgery/Topology/TracedRegionDeepNeckSupply.lean` (285 l.) — the in-lane discharge of `hdeep`:
`ObservedHistory.exists_tolerance_subseq_neckAlternative_of_isTracedRegion_uniform` (l.32) and the full-sequence
`…_eventually_…` (l.190); `TerminalHornSliceSelection.lean` (`exists_slices_of_deep_horn_presentation_sequence`, l.22).
No `sorry`.

VERIFIED (resolves the cycle-1/cycle-4 BLOCKER once wired into the leaf):
- Route is exactly SC8-1 at depth `T` with `Kb` (premise at `T' := T`) → SC8-2 line → neck at `yₙ` from
  `htopneck` (now a premise, cycle-4 RISK fix adopted) + `hwit` at the top slice → `exists_spatialNeck_of_pointed_spatialNecks_on_compact_ball`
  (α = 1/2000, radius `D+1`, R(basepoint)=1) → `SpatialNeck.simplyConnectedSpace_of_line` (accuracy 2α = 1/1000) →
  `exists_surface_product_on_closed_interval_of_line` on `[-(T'+T)/2, 0]` (handles `T' = 0`; cone, completeness,
  `Kb²` bound, nonflat from R(basepoint)=1 all from SC8-1 per layer) → SC8-4b along `f ∘ ψ`. The product is used
  only to exclude caps at traced witnesses; no neck at `y` is concluded from a finite window (H18 (2)/(5) respected).
  `etaD = min (1/1000) (neckModelTolerance (1/2000))` covers SC8-4b's `ε ≤ 1/1000`.
- Full-sequence wrapper: honest contradiction on a bad `σ₀`, all premises transferred along `σ₀`.
- `hwit` premise widened from `v < t n` to `v ≤ t n` (needed at the top slice); T4A-3's
  `extendAt_traced_limit_inputs` now delivers `≤` (RetainedCoreHistoryExtendAtLimitInputs.lean:58) — consistent.

FINDINGS:
- [RISK] Leaf still the conditional `fineCutNeckSupplyStrong_of_deep_layer_neck_supply` (unchanged since 16:45).
  Remaining step: add `fineCutNeckSupplyStrong_holds (P₀ g₀) : FineCutNeckSupplyStrong P₀ g₀` whose body
  instantiates `hdeep` from `exists_tolerance_subseq_neckAlternative_of_isTracedRegion_uniform` — but the binder
  shapes now DIFFER (the supply lemma has the extra premises `htop`, `htopneck` and `hwit` with `≤`), so the
  `hdeep` binders in the leaf / TerminalHornBlowupSequence / TerminalHornBlowupContradiction must be re-stated to the
  supply lemma's shape (or the leaf should drop `hdeep` and call the supply lemma directly). Then delete (or keep
  as private glue) the conditional theorem so no public conditional statement remains.

## Cycle 7 (17:27)

- TerminalHornBlowupContradiction.lean now obtains the deep supply from
  `ObservedHistory.exists_tolerance_eventually_neckAlternative_of_isTracedRegion_uniform` (l.144–145, used l.275) —
  the `hdeep` hypothesis is GONE from this layer (cycle-4 BLOCKER resolved there). TerminalHornBlowupSequence.lean
  restructured (`exists_tolerance_false_of_deep_horn_slices`, l.21), new `TerminalHornExtendAtTransports.lean`
  (5 transport lemmas), `TerminalHornSliceSelection.lean`. No `sorry`/overrides/comments.
- Lead-message normalization (log, latest): `Rₙ` = slice scalar at the base point, `hscal` exact, `τₙ ≥ a/2`
  eventually from `a ≤ sₙ` and `(sₙ−τₙ)·Rlₙ ≤ 1/(n+1)`; `Rₙ ≥ Rlₙ/2 → ∞`. Checked: consistent with SC8-1's
  basepoint-scalar-1 clause and with THBC's `Tendsto (R n * τ n)` input (cycle-1 NIT resolved).
- [RISK, carried] Leaf file unchanged since 16:45 (still the conditional
  `fineCutNeckSupplyStrong_of_deep_layer_neck_supply`); must become `fineCutNeckSupplyStrong_holds` without `hdeep`.

## Cycle 8 (17:40)

Leaf is now `fineCutNeckSupplyStrong_holds (P₀ g₀) : FineCutNeckSupplyStrong P₀ g₀` — UNCONDITIONAL
(Contract/FineCutNeckSupplyStrongLeaf.lean:18). The conditional `…_of_deep_layer_neck_supply` is gone; the cycle-2
converter was removed. Cycle-1/4 BLOCKER: RESOLVED.

VERIFIED (statement/constants, by reading):
- Conclusion is literally the def; no extra binders. `ε₁ = 1/30000`; `eta` = C1's `min eta₀ (min eta₇ eta₂)`;
  `εcone = min etaC (min epsW crossingNeckAccuracy)` with C2's `epsW = min epsW₀ etaD` (THBC.lean:146) and
  `etaD ≤ 1/1000` (TracedRegionDeepNeckSupply) ⇒ `εcone ≤ 1/1000`; neck accuracy `min (εc/(1+εc)) (1/12)`.
- `Kfine = n+1` by contradiction, chosen after `εc`, before `p₀`; `phi` and `a` depend only on `(P₀, g₀)`.
- Timeout split of old Lemma C into C1 (slice selection) / C2 (blow-up on `extendAt`) is at a genuine interface,
  no heartbeat override. No `sorry`/overrides/comments in any T4A file.

FINDINGS:
- [RISK] No axiom-closure evidence in the log yet. Before acceptance, the lane (scratch module, NOT committed)
  should record `#print axioms DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fineCutNeckSupplyStrong_holds`
  = only `propext`/`Classical.choice`/`Quot.sound` — the chain runs through ~15 UNCOMMITTED supplier modules
  (SC8 ×6, SC7, SC2, SC4, XA4…) compiled from copied scratch oleans; a stale scratch olean (Moise
  stale-olean lesson) would not show in per-file compiles. The acceptance build must compile the whole chain fresh
  in one `lake build` call.
- [NIT] Lint gate: the log's compile flag `-Dweak.linter.mathlibStandardSet=true` is right; confirm the final
  leaf and C1/C2 were compiled with it after their last edit (17:22–17:32).
- [NIT] Root aggregate: new public modules to register at acceptance (lead-side, not the lane):
  HistoryPinchingOfCutoffRecords, RetainedCoreHistoryExtendAt{StageTransfer,LimitInputs},
  HistoryStrongNeckStaggeredDepthInduction, HornPointSliceGeometry, TerminalHornBlowupContradiction,
  TerminalHornBlowupSequence, TerminalHornSliceSelection, TerminalHornExtendAtTransports, TracedRegionDeepNeckSupply,
  Geometry/Metric/Distance/SeparatedSideBallClause, Perelman/CanonicalNeighborhood/PointedSpatialNeckLimit,
  Contract/FineCutNeckSupplyStrongLeaf. Check name uniqueness of the public `extendAt_*` names library-wide.
