# OPUS fill log: brick CF

2026-09-26. Worker CF, worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf`).
No `lake build`, no git writes, `DifferentialGeometry.lean` untouched. No existing files modified.

## Result

- New file: `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/HistoryParabolicBallForwardFlow.lean`
  (245 lines), imports only `Surgery/Topology/HistoryParabolicBall`. Namespace
  `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory`, as in the sibling.
- Public theorem `exists_common_flow_past_time_of_parabolicallyRmControlledBall`. The statement is
  byte-identical to `DESIGN_C2_ASSEMBLY.md` §5.3 (checked with `diff`). It is proved with no `sorry`.
- Two private helpers:
  - `exists_closedSlab_stageMetric_of_lt_stageEndTime`: for `time k < s < stageEndTime k`, a
    `ClosedSlab` on stage `k` over `[time k, s]` whose metric is `stageMetric k` and whose initial
    value is `initialMetric k`. It comes from `closedPrefixAt ⟨s, _⟩` after `activeStage ⟨s, _⟩ = k`
    (`mem_stageDomain_iff`).
  - `exists_common_flow_past_time_of_parabolicallyRmControlledBall_aux`: the common flow on
    `closed a t₁` without the compact-neighbourhood clauses.
- Compile: `lake env lean` with `LEAN_NUM_THREADS=2` gives 0 errors and 0 warnings. A scratch copy with
  `linter.mathlibStandardSet true` and `#lint` gives no linter output, and `#lint` finds 0 errors in 3
  declarations with 14 linters. The scratch copy was deleted.
- `#print axioms` (scratch copy only): `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

## Route (B) as implemented

- `k := activeStage t`, `t₁ := (t + stageEndTime k)/2`, `t₂ := (t₁ + stageEndTime k)/2`. So
  `time k ≤ t < t₁ < t₂ < stageEndTime k`.
- `C := closedPrefixAt` up to `t₂` on stage `k` (helper). `G := C.restrictIncoming`,
  `L := C.endpointTerminalLimitMetric`. Then `terminalRegularRegion = univ`, so every point of the ball
  `U` lies in the incoming domain.
- The construction of `exists_backwardSurvivorIncoming_isSolutionOn` is re-run with this `G`, giving
  `gflow` on `[time first, t₂]`. The pullback to `U` along the same `Ψ` and tracing maps `f` is then
  time-restricted to `closed a t₁`.
- The stage-metric identification on `[a, t₁]` needs only the "before endpoint" case of
  `metric_eq_stage_pullback_of_backwardSurvivorIncoming`, because `v ≤ t₁ < t₂`. The old proof's
  terminal-endpoint branch disappears.
- The curvature bound `r⁴‖Rm‖² ≤ 1` is proved on `[a, t]` only, from the trace hypothesis. The terminal
  metric at `t` and the compact `K` with its frontier distance are proved as in
  `exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall`.
- Event times: nothing assumes `time k < t`. The slab runs from `time k ≤ t`, so `t = time k` (the
  post-surgery stage) is covered uniformly. The seam crossings come from `backwardSurvivorMap_crossing`
  as before.
- `ht` rules out `t = horizon` on the final stage: `stageEndTime_last = horizon`
  (`HistoryAction.lean:28`).

## Deviations

- None in the statement.
- Route detail: the digest says "closedPrefixAt up to `t₁`". The implementation takes the closed
  prefix up to an auxiliary `t₂ ∈ (t₁, stageEndTime k)` and restricts to `[a, t₁]`. This avoids the
  endpoint case of the metric identification. It is still route (B): the same `U` and `f`, with the
  survivor-incoming construction re-run. It does not enlarge the old flow or glue by metric equality.
- The file has no copyright header and no module docstring, following every sibling in
  `Surgery/Topology/` (592 of 593 files have no header). `linter.style.header` is off in `lakefile.toml`.
