# B4 — backward step (2026-09-26)

- Wrote `Surgery/Topology/TracedRegionBackwardStep.lean` (imports CrossingRoom + Estimates.CurvatureMetricComparison;
  X2's BackwardTraceDistortion has no olean and its distortion lemmas are private, so a stage-local
  distortion lemma is proved here from the public `metric_inner_exp_bounds_of_curvature_bound`).
- First compile attempt: missing olean `Perelman/CanonicalNeighborhood/TerminalBackwardSlabConstruction`
  (a lake build is running in this worktree); retrying every 10 min.
- Retry 2: missing olean Surgery/Topology/CanonicalNeighborhoodInduction (build still running); retry 3 scheduled.
- Retry 3: compiles clean (`LEAN_NUM_THREADS=2 lake env lean`, 0 diagnostics). Scratch copy: 9 public
  theorems depend only on propext/Classical.choice/Quot.sound; `#lint` 14 linters, 0 errors. Scratch removed.
- Public API (ns `...Surgery.Topology`): `ObservedHistory.activeStage_eq_of_forall_time_not_mem_Ioc`,
  `ObservedHistory.stageMetric_inner_le_exp_of_normSq_le`, `RetainedCoreHistory.`{
  `scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_at`, `..._of_scalar_le_above`,
  `normSq_rm_le_of_backwardPointTrace_of_scalar_le_two_mul`,
  `isRmControlled_of_backwardPointTrace_of_scalar_le_two_mul`,
  `exists_backwardPointTrace_scalar_le_two_mul_of_backward_step` (hdepth: 8·Ctime·QR₀·(u−u') ≤ 1),
  `..._of_depth_eq` (u' = u − 1/(8·Ctime·QR₀)), `..._of_backward_step_of_no_event` (+ distortion)}.
- Not wired into the root aggregate (lead's call). Crossing an event needs the trace to u' as hypothesis
  (`htrace`); X2's cross-event distortion lemmas are private — distortion here is stage-local only.
