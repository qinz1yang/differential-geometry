# B2 — traced regions and the common survivor flow (2026-09-26)

New file `Topology/TracedRegion.lean` (only file touched besides this log). Not lake-built, not
registered in `DifferentialGeometry.lean` (lead).

## Deviations from DESIGN_CROSSING B2a (read first)

- Names are lower camel (`isTracedRegion`, `isRmBoundedBy`, `isTerminalTracedRegion`): NAMING.md §2
  (defs are lower camel), matching `isParabolicallyRmControlledBall`; the design's theorem name
  `exists_common_flow_of_isTracedRegion` already uses the lower token. B5's `H.IsTracedRegion` is
  `H.toHistory.isTracedRegion` (predicate lives on `ObservedHistory`, as in B2a).
- The predicate carries `0 < τ` besides `0 < ρ`: needed for the common flow when `t` is an event
  time (`first < last`); every consumer has depth `T/R > 0`. Bridge:
  `isParabolicallyRmControlledBall t p r ↔ isTracedRegion t p r (r^2) (r^2)⁻¹` (unconditional).
- Terminal slab = the extended history `H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG`,
  the same object `TerminalNoncollapsedBefore` uses (so B6's κ input and B2's flow live on one history).
  The base `p : (H.stage (Fin.last _)).Carrier` enters by `cast` along
  `activeStage_extendHorizon_eq_last`; stage-explicit theorems take `q` with `HEq q p`.

## Public API

- `BackwardPointTrace.isRmBoundedBy A K`: `normSq0S ≤ K^2` along the trace and at every crossing.
  `isRmControlled_iff_isRmBoundedBy (hr : 0 < r) : isRmControlled r ↔ isRmBoundedBy (r^2)⁻¹`;
  `isRmBoundedBy.mono`, `.restrictFirst`.
- `ObservedHistory.isTracedRegion t p ρ τ K`; `.radius_pos`, `.depth_pos`, `.depth_le_time`,
  `.mono` (all three at once), `.mono_radius`, `.mono_depth`, `.mono_bound`, `.normSq_le`.
- `exists_common_flow_of_isTracedRegion`: exactly the B2b shape (time range `[t−τ, t]`, maps `f`,
  local diffeos, injective, `RegularCrossing` at every crossed event, `f last = val`,
  `IsSolutionOn S`, metric = pullback of the stage metric, `normSq0S (S v) ≤ K^2`).
- `exists_common_flow_with_compact_neighborhood_of_isTracedRegion`: adds
  `∀ v ∈ Icc a t, v ∈ stageDomain (activeStage t) → S v = (stageMetric _ v).restrictOpen U` and the
  compact `C` over the closed ball of radius `ρ/2` with frontier separation (as the tied version).
- `exists_stage_common_flow_with_compact_neighborhood_of_isTracedRegion` (`hk : activeStage t = k`),
  `exists_event_common_flow_with_compact_neighborhood_of_isTracedRegion` (event slab, metric clause
  `S v = ((event i).incoming.flow.base.metric v).restrictOpen U` for `time i.castSucc ≤ v`),
  `mem_stageDomain_castSucc_of_activeStage_eq`.
- Terminal: `RetainedCoreHistory.isTerminalTracedRegion hend G hG hT hTs p ρ τ K` with
  `.radius_pos/.depth_pos/.depth_le_time/.mono/.mono_radius/.mono_depth/.mono_bound/.normSq_le`
  (the last on `G.flow.base.metric T`), and
  `exists_common_flow_with_compact_neighborhood_of_isTerminalTracedRegion` (U = ball of
  `G.flow.base.metric T`, `S v = (G.flow.base.metric v).restrictOpen U` for `time last ≤ v`);
  helpers `activeStage_extendHorizon_eq_last`, `stageMetric_extendHorizon_last`.
- Producer (B4 output shape, event and final slab): `RetainedCoreHistory.
  isRmBoundedBy_of_backwardPointTrace_of_derivative_bounds` and
  `isTracedRegion_of_forall_nonempty_backwardPointTrace` (separate `ρ, τ`, `K = 8√3(1+φ1+φ0)M`),
  the `isRmControlled`/tied CrossingRoom lemmas generalized.
- Terminal ports of the CrossingRoom hypotheses on the extended history:
  `eventSlabsPinched_extendHorizon`, `eventSlabsDerivative_extendHorizon`,
  `eventSlabsGradient_extendHorizon`, `extendHorizon_finalSlab_phiAlmostNonnegative` (the `hlast`
  input), `extendHorizon_finalSlab_derivativeBoundBefore` (the `hfinal` input),
  `extendHorizon_finalSlab_gradientBoundBefore`. With these every CrossingRoom lemma (which already
  carries `hlast`/`hfinal`) applies verbatim to the terminal slab.

## Shapes matched (DESIGN_CROSSING)

- B2b: "`∃ a hat, a.val = t.val - τ ∧ ∃ U, U = riemannianBallOf … p ρ ∧ ∃ f … RegularCrossing …
  f last = val ∧ ∃ S, IsSolutionOn S ∧ pullback ∧ normSq0S (S.base.metric v) x 4 … ≤ K ^ 2`" —
  verbatim.
- B4: "Output `IsTracedRegion t y (A/√R) (Δ) (K·Q·R)`" — `isTracedRegion_of_forall_nonempty_
  backwardPointTrace` with `ρ = A/√R`, `τ = Δ`, `M = 2QR`-type bound.
- B5: "`H.IsTracedRegion t y (A/√R) (T/R) (K(phi)·2Q·R)`" with `y` in `stage (activeStage t)`.
- B6b/B8b: "the survivor flow on `U` equals `G.flow` restricted to `U` (`f last = val`)" — the
  restrictOpen clauses of the event/terminal compact-neighbourhood theorems.

## Not done

- X2 terminal port (`exists_cap_capture_of_ball_point_without_trace`,
  `capWindowPoint_of_ball_point_without_trace`, `exists_parabolicallyRmControlledBall_or_capWindowPoint`
  on the final slab). X2 uses `hi : activeStage t = i.castSucc` in two private places (the `hne`
  scalar control and `initialMetric_inner_le_exp_of_normSq_le` on the event flow). Recommended fix in
  X2 itself: replace `hi/hcurrent` by CrossingRoom's `hcurrent/hfinal/hlast` triple; the terminal case
  is then the `extendHorizon` instance fed by the transfer lemmas above. Not copied here (would
  duplicate ~400 lines of X2 private code).
- The tied `exists_common_flow_of_parabolicallyRmControlledBall` (HistoryParabolicBall) is now a
  one-line corollary via `isParabolicallyRmControlledBall_iff_isTracedRegion`; refactoring it is left
  to the lead (edit-nothing-else rule).
