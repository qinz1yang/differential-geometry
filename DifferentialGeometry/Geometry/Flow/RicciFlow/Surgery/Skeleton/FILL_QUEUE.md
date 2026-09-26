# Fill queue — Poincaré endgame leaves and bricks (2026-09-26)

Execution queue only. Acceptance and proof debt belong to `../FREE_INPUTS.md`. Worktree
`D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf` (mirror `liao`). Workers create new
modules, compile read-only with `LEAN_NUM_THREADS=2 lake env lean <file>`, never run `lake build`,
never write git, log to `OPUS_FILL_LOG_<x>.md` in this folder. At most four worker compiles at once
while a lead build runs (host budget). The lead builds, audits (13 linters + axioms), wires, commits.

Leaves (sorry, `PoincareEndgame.lean`): S `uniformDebitSurgeryStep`; C2 `noncollapsingThroughSurgery`
(being split, entry 2); C3a `deepContinuation`; C3b `capWindowContinuation`; C3c `crossingContinuation`.

| # | Entry | Lane | Status |
|---|---|---|---|
| 1 | CapWindow half 1: `CapWindowPoint` ⇒ standard-solution comparison at the point (`exists_uniform_prepared_cap_common_flow_of_backward_trace`), then derivative and gradient bounds from `C^N` closeness | W1 | running |
| 2 | C2 split: `reducedVolume` on the collaborator's `regularizedDensity`; leaves monotone / local upper bound / initial lower bound / cap barrier; assembly proved | K2 | running |
| 3 | Crossing feasibility: complete ancient limit from `IncompleteLocal` + `TracedTerminalCompactness`; young-point neck structure — must the induction predicate change? | X1 | running (analysis) |
| 4 | S port feasibility: factory binder reorder per input; CN uses and their ages; FIX 3 cutting scale | S2 | running (analysis) |
| 5 | Deep leaf assembly: `deepContinuation` from `HistoryNoncollapsingToSlab` (G), the parabolic wrappers `exists_uniform_canonicalOn_of_parabolically_noncollapsed(_of_le_age)`, `SlabPointPicking`, `SlabBackwardCurvatureControl`, `ForwardTransfer`, `InitialSlabUniformBounds`; forward noncollapsing on `(t₀, t₀ + η)` by the slab's global curvature bound and forward transfer | E1 | open |
| 6 | Stage 0: discharge `exists_uniform_kappaNoncollapsed_initial`'s per-slab `NoLocalCollapsing` hypothesis by components (`ComponentBallTransfer`, `no_local_collapsing` with `[ConnectedSpace]`) | E2 | open |
| 7 | CapWindow half 2: transport of the cap alternative and the `gradient`/`time_derivative` fields under one `MetricComparisonOn` (generalize the time-0 sources `StrongNeck.transport'`, `orderedNeckChainTransport`, `LocalCap.map`; ball sandwich; cap depth margin) | E3 | open (after the M2 build) |
| 8 | Class constraints: `p₀.recenterConstant ≤ Λ` and `a₀` pinching of `g₀` in `InCutoffClass` and the leaves (interface edit) | lead | open |
| 9 | Replace the private duplicate in `SlabGradientScalarControl` by `IncomingSlab.scalar_le_two_mul_of_derivativeBoundBefore` (`BackwardTraceScalarControl`) | any | open, mechanical |
| 10 | Crossing bricks (after entry 3's verdict) | — | blocked on 3 |
| 11 | S port (after entry 4's verdict): factory chain, age-restricted CN, cutting scale `h/√(C·Ctime·τmin)` | — | blocked on 4 |
| 12 | C2 leaf bricks (after entry 2) | — | blocked on 2 |
