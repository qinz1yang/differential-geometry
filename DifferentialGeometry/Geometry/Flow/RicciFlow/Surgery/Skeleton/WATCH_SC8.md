# WATCH SC8 (advisory watcher, read-only)

## Cycle 1 (2026-09-26 16:25 PDT) — state: SC8-5a, 5b, 2, 1, 4a, 4b logged PROVED; SC8-3 file written, not yet logged compiled

Checked: SC8-1 `exists_window_pointed_flow_limit_of_isTracedRegion` (TracedRegionWindowLimit.lean:82) gives
`Rm ≥ 0` on `Ioc (-T) 0`, completeness of every slice incl. 0, `MetricComplete P`, `ConnectedSpace P.M`,
uniform `curvDerivNormSq 0 (G s) ≤ K²`, `IsSolutionOn` on `openClosed (-T) 0`, κ clause — OK.
No `sorry`/heartbeat/`nolint`/diagnostics in the seven SC8 files. No age hypothesis: the only
`Tendsto (R n * _)` is `hsliver` (`t₀ = t` in T4′, sliver 0). SC8-5b's `Qup` (`C₀`) is quantified before
`∀ A` — truly uniform (along a subsequence `ψ`). Cited suppliers all exist at the cited names.

- **BLOCKER (assembly, not SC8's files): committed SC6-c cannot consume SC8-4b.**
  `HistoryStrongNeckDepthInduction.lean:133` `hsupply` has (i) premise `∀ A T', … ∃ K` (K radius-dependent;
  SC8-1 needs `K` before `∀ A`), (ii) conclusion with the closed bottom `t − T/Rₙ ≤ v` at the SAME `T` as the
  premise (SC8-4b gives only `T' < T`), (iii) `∀ᶠ n` along the full sequence (SC8-4b gives `∀ᶠ i` along
  `f ∘ ψ`). Fix: a NEW-file variant SC6-c′ (do not edit the committed file) with
  `hsupply' : ∀ T > 0, (∃ K ≥ 0, ∀ A > 0, ∀ᶠ n, isTracedRegion … (T/Rₙ) (K*Rₙ)) → ∀ T', 0 ≤ T' → T' < T → <SC8-4b's conclusion shape on the full sequence>`,
  base case `T = 0` from `hneck` (top slice, as SC8-5a), step: traced at `D` (uniform `K := 8√3(1+φ1+φ0)·max Qup 1`)
  ⇒ supply at `D − δ/2` ⇒ SC6-b at `D − δ/2` ⇒ traced at `D + δ/2`, `δ = (10·Qup)⁻¹`. The subsequence→full
  step: `by_contra` + `Filter.extraction_of_frequently_atTop` (as in SC8-4b:~290), then SC8-1 on `H ∘ σ`
  (htraced transfers via `σ`'s `StrictMono.tendsto_atTop`), product (SC5-1b + SC8-3 + SC8-2), SC8-4b, and a
  common index for the contradiction. Somebody must own this theorem; the log currently only says
  "assembly theorem records SimplyConnectedSpace P.M as the remaining input".
- **RISK: `hnonflat` of SC5-1b is not among SC8-1's outputs.** `exists_surface_product_on_closed_interval_of_line`
  (DimensionThree/LineProductSplitting.lean:83) needs `∃ x, metricRm04At (S.base.metric 0) x ≠ 0`. Supply it from
  the basepoint scalar: `hball`'s lower half gives `Qlow·Rₙ ≤ R(yₙ)`; transport with
  `tendsto_metricScalarAt_of_metricDerivNormSupOn` (Perelman/StandardSolution/StandardWindowShiftConvergence.lean:24)
  or `MetricCPConvergenceOn.tendsto_metricScalarAt_sub_of_eventually_mem`
  (Compactness/CheegerGromov/Limit/Metric/ScalarConvergence.lean:96). Suggest a hypothesis-conditioned clause
  `Qlow ≤ metricScalarAt P.metric P.basepoint` in SC8-1 or a separate brick.
- **RISK: SC5-1b's `hbound` form vs SC8-1's.** SC5-1b wants `normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K`;
  SC8-1 states `curvDerivNormSq 0 (G s) x ≤ K²` and the bridge `curvDerivNormSq_zero_eq_normSq0S` is PRIVATE
  (TracedRegionWindowLimit.lean:42). The assembly file cannot use it without `open private`. Either restate the
  limit clause in SC5-1b's `normSq0S` form, or make the bridge public (check the name is unique).
- **RISK: the neck input of SC8-3 (`SpatialNeck (G 0) eps p`).** B9w
  `neck_alternatives_of_local_flow_limit_on_window` (AncientPointedFlowLimitWindowNeckAlternatives.lean:214)
  fires only at points with `4 * max q 1 < R(x)` — the `1` is hard-coded, and the limit scalar near the
  basepoint lies in `[Qlow, Qup]` with only `1 ≤ Qup` known. Also B9w's `hW` needs neck-ALTERNATIVES
  (`Nonempty SpatialNeck ∨ … ∨ IsCompact (connectedComponent z)`) on ALL window slices, not just `s = 0`.
  Cheapest fix: since `SimplyConnectedSpace` is metric-independent, apply SC8-3 to `g := scaleMetric c (G 0)`
  (completeness, `Ric ≥ 0`, and the line reparametrized by `√c` are scale invariant) with a neck obtained at a
  point of scalar `> 4` of the rescaled metric, or use `SpatialNeck.scaleMetric` (Geometry/Neck/Spatial.lean:58)
  to move a neck between scales. Consider the time-0-only transfer used by XA4
  (`AncientPointedFlowLimitTransfer.lean:440` route) instead of the window B9w. The third alternative
  `CompactSpace P.M` must be excluded by the line (no supplier found by grep; ~10 lines: bounded diameter vs
  `ofReal |s − t|`).
- **RISK (integration order):** SC8-4b imports the uncommitted XP2′ `Surgery/Topology/LocalFlowLimitWindowTransfer.lean`;
  SC8-4b cannot be accepted before XP2′ is.
- **NIT:** private `diffeomorphOfOpensEq` (+ `_val`, `mfderiv_`) duplicated in LocalPullProductNeck.lean and
  Geometry/Neck/LineNeckSimplyConnected.lean — deferred merge into `Topology/Manifold/PartialDiffeomorph/Opens.lean`.
  Also the `open private` uses from committed `TracedRegionAncientLimit` / `AncientPointedFlowLimitShiftedTransfer`
  and the private `Opens` instances: record as deferred merges (fine per the no-import-chain-edit rule).
- **NIT:** LineNeckSimplyConnected.lean opens `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology` from a
  `Geometry/Neck/` file that imports no Surgery module — likely an unused open; drop it.
- **NIT:** SC8-4b allows `T' = 0` but its product input then comes from SC5-1b only for `a < b`; for the
  assembly use `0 < T' < T` (no issue, just note that `T' = 0` needs Cheeger–Gromoll at time 0 instead).
- Info: `git status` shows modified committed files `DifferentialGeometry.lean`,
  `Surgery/Skeleton/PoincareEndgame.lean`, `ACC13_LOG.md` — not in SC8's file list (probably ACC lanes); lead to
  confirm SC8 did not touch them.

## Cycle 2 (2026-09-26 16:36 PDT) — log now has Deliverables / Deviations / "assembly still lacks"; SC8-3 being extended

Resolved since cycle 1: `not_compactSpace_of_line` added (LineNeckSimplyConnected.lean:104) — excludes B9w's third
alternative; the unused `Surgery.Topology` open became a selective `open … (ThreeSpace Sphere)`; `hnonflat`
supplier named in the log (`metricScalarAt_basepoint_eq_of_local_flow_limit`,
AncientPointedFlowLimitBaseScalar.lean:31 — exists). Axioms of six headlines recorded (standard three).

- **BLOCKER (still open, now partly misdescribed in the log):** "What the T4′ final assembly still lacks" item 1
  proposes "one line each in `HistoryStrongNeckDepthInduction.lean`". That file is COMMITTED (d9106490c) and
  sits in SC6-d's import chain — editing it violates "new files only" and triggers a rebuild of its dependants.
  Put SC6-c′ in a NEW file. And the list omits interface change (iii): SC8-4b concludes `∀ᶠ i` along `f ∘ ψ`
  (the window limit's subsequences), whereas SC6-c's `hsupply` needs `∀ᶠ n` along the whole sequence it
  is applied to. SC6-c′ (or the assembly) must contain the subsequence→full-sequence argument: `by_contra`,
  `Filter.extraction_of_frequently_atTop` to a bad `σ`, SC8-1 + SC5-1b + SC8-3 + SC8-4b on `H ∘ σ`, then
  pick `i` with `σ`-index in both the bad set and SC8-4b's eventual set. This needs ALL SC8-1/SC8-2/SC8-3
  inputs (traced region, κ, pinching, the separating-set `hpoints`, the top-slice necks) to hold on every
  subsequence — true for `∀ n` / `∀ᶠ n` hypotheses, but the assembly must state them in that form, not along
  SC8-5b's fixed `ψ` only (apply SC6-c′ to `H ∘ ψ` and do the extraction inside that).
- **RISK:** `#print axioms` not yet recorded for `SpatialNeck.simplyConnectedSpace_of_line`,
  `SpatialNeck.exists_diffeomorph_sphere_of_product_structure`, `not_compactSpace_of_line` (the file changed
  after the recorded axiom run) — record after its final compile.
- **RISK:** `hnonflat` via X5d's basepoint-scalar lemma gives scalar `1` only if `R n = R(yₙ)` (the blow-up
  normalizes at `yₙ`); if the T4′ `Rₙ` is a different normalization, use `hball`'s `Qlow` half instead.
  The lead should confirm which `Rₙ` T4A uses.
- **NIT:** `not_compactSpace_of_line` is a generic metric fact (any model, any metric) but lives in namespace
  `…Perelman.CanonicalNeighborhood.FiniteHorn` in a `Geometry/Neck/` file. Move it (at acceptance) to the
  splitting/line home, e.g. `Geometry/Comparison/Splitting/IntrinsicLine.lean`'s namespace
  `DifferentialGeometry.Geometry.Topology` (new file next to it), generalized from `I3` to any boundaryless model.
- **NIT:** acceptance must first build the unbuilt committed chain `IntrinsicLine`, `Busemann`,
  `AffineFunctionSplitting`, `AffineZeroLevelCompleteness` (log notes it) — relay to the ACC lane.

## Cycle 3 (2026-09-26 16:47 PDT)

Resolved: SC8-1 now states the limit bound in SC5-1b's form `normSq0S (G s) x 4 (metricRm04At (G s) x) ≤ K²`
(TracedRegionWindowLimit.lean:189) and adds `(∀ n, R(yₙ) = Rₙ) → metricScalarAt P.metric P.basepoint = 1`
(:191–193, `hnonflat` source; conditional on the normalization — honest, not packaged). SC8-3 gained
`SpatialNeck.simplyConnectedSpace_of_line_of_scaleMetric` (LineNeckSimplyConnected.lean:171; neck of
`scaleMetric c g`, line reparametrized by `√c`) — resolves the `4·max q 1` threshold concern; and
`not_compactSpace_of_line` is generalized to any model `I`/`X` (:113).

- **BLOCKER (unchanged):** SC6-c′ in a NEW file (uniform `K` premise, `T' < T` margin, subsequence→full
  extraction); log item 1 still says "edit `HistoryStrongNeckDepthInduction.lean`". Not SC8's scope unless
  the lead assigns it.
- **NIT:** `not_compactSpace_of_line` is now fully generic but still in namespace `…FiniteHorn` — move at
  acceptance (see cycle 2).
- **NIT:** new `Surgery/Topology/LocalFlowLimitBaseScalar.lean`
  (`metricScalarAt_basepoint_eq_of_local_flow_limit_on_window`) appeared; if it is SC8's, add it to the
  Deliverables table with its acceptance order; it looks like a window twin of X5d's
  `metricScalarAt_basepoint_eq_of_local_flow_limit` (AncientPointedFlowLimitBaseScalar.lean:31) — check it
  is not a duplicate (grep the statement shape; deferred merge if one generalizes the other).

## Cycle 4 (2026-09-26 16:58 PDT) — log unchanged (374 lines); SC8-1 now imports `LocalFlowLimitBaseScalar`

- **RISK (duplication):** `metricScalarAt_basepoint_eq_of_local_flow_limit_on_window`
  (Surgery/Topology/LocalFlowLimitBaseScalar.lean:31, new) is a strict generalization of the committed X5d
  `metricScalarAt_basepoint_eq_of_local_flow_limit` (AncientPointedFlowLimitBaseScalar.lean:31): same
  binders except window `Icc (-c k) 0` with `0 ≤ c 0` instead of `Icc (-(k+1)) 0`, and `hW0` only at
  `k = 0`; same proof skeleton and the same private `Opens` instance. Record it in the log as a DEFERRED
  MERGE: X5d's theorem becomes a one-line corollary (`c k := k+1`, `hW0 0`) of the window version at
  acceptance; add the file to the Deliverables table (acceptance order: before `TracedRegionWindowLimit`).
- **BLOCKER (unchanged):** SC6-c′ (new file; uniform `K`, `T' < T` margin, subsequence→full extraction); log
  "assembly still lacks" item 1 still proposes editing the committed `HistoryStrongNeckDepthInduction.lean`.
- **RISK (unchanged):** axioms of the SC8-3 declarations and the re-edited SC8-1 not re-recorded after the
  last edits — re-run `#print axioms` on the final versions.

## Cycle 5 (2026-09-26 17:09 PDT) — lane FINISHED (log "Final status"); watcher stops

Verified in the final status: SC8-3 split without heartbeat override; axioms of all 13 public declarations
standard; no committed file modified; `hnonflat` route via `metricScalarAt_eq_zero_of_metricRm04At_eq_zero`.

Open items for the lead (carried to the final report):
- **BLOCKER:** SC6-c′ does not exist. Needed in a NEW file: `hsupply` premise with a UNIFORM `K`
  (`∃ K ≥ 0, ∀ A > 0, ∀ᶠ n, isTracedRegion … (T/Rₙ) (K*Rₙ)`), supply only for `T' < T`, depth step `δ/2`,
  and the subsequence→full-sequence extraction (SC8-4b concludes along `f ∘ ψ`). The log's "assembly still
  lacks" item 1 still says to edit the committed `HistoryStrongNeckDepthInduction.lean` — do not.
- **RISK:** SC8-1's base-scalar clause is conditional on `∀ n, R(tₙ, yₙ) = Rₙ`; T4A normalizes by
  `Rₙ := R_L(xₙ)`, so the assembly must either renormalize at the slice scalar or add the inequality form
  (`Qlow ≤ R(base)`) — the log calls it "not needed", but it is only unneeded if the renormalization is done.
- **RISK (duplication, deferred merge not yet recorded in the log):** X5d's committed
  `metricScalarAt_basepoint_eq_of_local_flow_limit` should become a corollary of the new
  `…_on_window` version at acceptance.
- **NIT:** `not_compactSpace_of_line` (generic) lives in namespace `…FiniteHorn`; move at acceptance. Duplicated
  private helpers (`diffeomorphOfOpensEq` ×2, `depth_schedule_facts` ×2, `Opens` instances ×6+,
  XP2′ shifted-convergence copy) are deferred merges.
- **Acceptance:** build the unbuilt committed `IntrinsicLine`/`Busemann`/`AffineFunctionSplitting`/
  `AffineZeroLevelCompleteness` chain first; order per the log's Deliverables table, with
  `LocalFlowLimitBaseScalar` before `TracedRegionWindowLimit`.
