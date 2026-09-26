# Fill queue — Poincaré endgame leaves and bricks (2026-09-26)

Execution queue only. Acceptance and proof debt belong to `../FREE_INPUTS.md`. Worktree
`D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf` (mirror `liao`). Workers create new
modules, compile read-only with `LEAN_NUM_THREADS=2 lake env lean <file>`, never run `lake build`,
never write git, log to `OPUS_FILL_LOG_<x>.md` in this folder. At most four worker compiles at once
while a lead build runs (host budget). The lead builds, audits (13 linters + axioms), wires, commits.

Leaves (sorry, `PoincareEndgame.lean`, strong interface since 2026-09-26): S `uniformDebitSurgeryStepStrong`;
C2 `historyReducedVolumeMonotone`, `historyReducedVolumeLocalUpperBound`,
`historyReducedVolumeInitialLowerBound`, `smallScaleNoncollapsingThroughSurgery`; C3b
`capWindowContinuation`; C3c `crossingContinuation`; C4 `spatialCanonicalContinuation`. C3a
`deepContinuation` is proved (`Topology/DeepContinuation.lean`).

| # | Entry | Lane | Status |
|---|---|---|---|
| 1 | CapWindow half 1: `CapWindowPoint` ⇒ standard-solution comparison at the point (`exists_uniform_prepared_cap_common_flow_of_backward_trace`), then derivative and gradient bounds from `C^N` closeness | W1 | half done (`CapWindowStandardComparison`, `exists_standard_comparison_of_cap_window_trace`) |
| 2 | C2 split: `reducedVolume` on the collaborator's `regularizedDensity`; leaves monotone / local upper bound / initial lower bound / cap barrier; assembly proved | K2 | running |
| 3 | Crossing feasibility: complete ancient limit from `IncompleteLocal` + `TracedTerminalCompactness`; young-point neck structure — must the induction predicate change? | X1 | running (analysis) |
| 4 | S port feasibility: factory binder reorder per input; CN uses and their ages; FIX 3 cutting scale | S2 | running (analysis) |
| 5 | Deep leaf assembly: `deepContinuation` from `HistoryNoncollapsingToSlab` (G), the parabolic wrappers `exists_uniform_canonicalOn_of_parabolically_noncollapsed(_of_le_age)`, `SlabPointPicking`, `SlabBackwardCurvatureControl`, `ForwardTransfer`, `InitialSlabUniformBounds`; forward noncollapsing on `(t₀, t₀ + η)` by the slab's global curvature bound and forward transfer | E1 | done (`Topology/DeepContinuation.lean`, `deepContinuation`; wired) |
| 6 | Stage 0: discharge `exists_uniform_kappaNoncollapsed_initial`'s per-slab `NoLocalCollapsing` hypothesis by components (`ComponentBallTransfer`, `no_local_collapsing` with `[ConnectedSpace]`) | E2 | done (`Topology/InitialSlabNoncollapsing.lean`, `exists_uniform_kappaNoncollapsed_initial_of_pos`) |
| 7 | CapWindow half 2: transport of the cap alternative and the `gradient`/`time_derivative` fields under one `MetricComparisonOn` (generalize the time-0 sources `StrongNeck.transport'`, `orderedNeckChainTransport`, `LocalCap.map`; ball sandwich; cap depth margin) | E3 | done (the five sources generalized in place to a general time `t₀`; `CapComparisonTransport` (`LocalCap.exists_deep_transport_tolerance_of_metricComparisonOn`), `CanonicalAlternativeComparisonTransport` (neck and cap alternatives; positive and round need a global component equality)) |
| 8 | Class constraints: `p₀.recenterConstant ≤ Λ` and `a₀` pinching of `g₀` in `InCutoffClass` and the leaves (interface edit; fold into 13) | lead | open |
| 9 | Replace the private duplicate in `SlabGradientScalarControl` by `IncomingSlab.scalar_le_two_mul_of_derivativeBoundBefore` (`BackwardTraceScalarControl`) | any | open, mechanical |
| 10 | Crossing bricks (after entry 3's verdict) | — | blocked on 3 |
| 11 | S port (after entry 4's verdict): factory chain, age-restricted CN, cutting scale `h/√(C·Ctime·τmin)` | — | blocked on 4 |
| 12 | C2 leaf bricks (after entry 2) | — | blocked on 2 |
| 13 | Interface revision (third review): `SpatialCanonicalWitness` (age-free, four alternatives on `SpatialNeck`) with `CanonicalWitness.toSpatial`; strong joint C output (gradient clause, spatial clause, κ via `TerminalNoncollapsedBefore`) with old C as projection; S restated `∀ B Ctime, ∃ ε, …` consuming the spatial clause; assembly on the strong C; Λ, a₀ class constraints | lead design | 13b wired: strong interface (`CanonicalNeighborhoodsThroughSurgeryStrong`, `UniformDebitSurgeryStepStrong`, C4 `SpatialCanonicalContinuation`) is the skeleton path |
| 14 | Deep-horn neck improvement (Perelman II 4.3 / KL 71): minimizing-arms hypothesis, cylinder limit, δ-neck at the point | H | done (`HornNeckImprovement`, `exists_strongNeck_threshold_of_minimizing_arms`) |
| 15 | Design extraction for 13: exact shapes of `SpatialNeck`, `LocalCap`, positive/round alternatives, factory's witness field uses | — | running (analysis) |
| 16 | `ProspectiveNeckSurvival` with a variable threshold sequence `q₀ₙ/Qₙ → 0` (output `Qmin = Λ·max q₀ 1`) | — | done (`ProspectiveNeckSurvivalVariableThreshold`, `exists_threshold_uniform_selected_neck_append_backward`) |
| 17 | Factory: replace the five `W.time_derivative` reads by the derivative clause | — | open, mechanical 150–300 |
| 18 | Deep-horn arms: single-neck version delivered (`NeckRegionAxialArms`); chain version at fixed accuracy (18b `NeckChainAxialArms`) | A / A2 | done (18 and 18b) |
| 18c | Deep-horn arms from a local neck chain around the point (no root, scalar comparability inside the chain) | A3 | done (`Topology/LocalNeckChainAxialArms.lean`, `IncomingSlab.exists_strongNeck_threshold_of_localNeckChain`) |
| 19 | `CapWindowPoint` margin `‖x‖ < Dcap + 1`, cap-window leaf outputs `Rcap` | W19 | done |
| 20 | CapWindow D2: derivative and gradient bounds at the cap point from `C^N` closeness (jets → bounds, scaling transport) | D2 | done (`Topology/CapWindowDerivativeBounds.lean`, `RetainedCoreHistory.exists_derivative_gradient_bounds_of_cap_window_trace`; order-`j` standard-cap bound in `StandardCurvatureComparison`) |
| 21 | Crossing room lemma: `¬ CapWindowPoint` ⇒ parabolically controlled ball of radius `c/√R` | X1 | 10a partial (`CrossingRoom`) |
| 21b | Room lemma on event slabs: backward-trace distortion, cap capture of an untraceable ball point, `exists_parabolicallyRmControlledBall_or_capWindowPoint` | X2 | done (`Topology/BackwardTraceDistortion.lean`; event-slab case `activeStage t = i.castSucc` only) |
| 21c | Room lemma on the final slab (`Topology/BackwardTraceDistortionTerminal.lean`) | X2b | running |
| 22 bricks | H0 (`Topology/HistoryScalarFloor.lean`), G7 (`Analysis/Integration/Measure/Parametric/`), G8 (`Perelman/Noncollapsing/`), G4 (`Perelman/LGeometry/Index/`) per `DESIGN_22.md` | H0 / G7 / G8 / G4 | running |
| 22 decision | Closed ends of the history time window | lead | decided: handled by brick G1 (closed-end time extension, `DESIGN_22.md`) |
| 22 | C2 tools (OURS, after C): history L-exponential map for regular-crossing minimizers; Jacobian monotonicity of `regularizedDensity` through events; local upper bound / Gaussian tail (12a's bricks 1–3) | — | open, after C |
| 24a / 24b | Initial lower bound: cap-point action barrier (24a), positive-volume initial block (24b) | — | blocked on entry 23 (`ANALYSIS_ILB.md`) |
| 26 | Reduced-volume truncation: stage scalar floor, independence of the truncation `B`, finiteness, measurability of `regularizedDensity` from closed cost sublevels | RV | done (`Topology/ReducedVolumeTruncation.lean`); measurability of `regularMinimizerEndpoints` open |
| 27a | Standard solution's spatial canonical witnesses on `[0, Θ]`: old region by projection, young region as the named hypothesis `StandardSolution.YoungSpatiallyCanonical` | SW | done (`StandardSolution/StandardSpatialCanonical.lean`; general constant enlargement in `SpatialCanonicalWitness`) |
| 27b | `StandardSolution.YoungSpatiallyCanonical`: far necks at positive time, tip caps at every `t ≤ Θ`, uniform witness fields | 27b | running |
| 28 | Interface revision (`DESIGN_28.md`): class supply, `ρmax` after `qcan`, spatial clause into the small-scale and crossing leaves, fixed core `D*`, variable threshold | I28 | done (accepted by ACC3: `InCutoffClass` conjunct `recenterConstant * δbound ≤ 1/2`; S takes `εbar`, C is `∃ εbar`; C4 outputs `Cs`, floor `q₄`; contracts threshold-ordered; old C assembly deleted; 8 sorry leaves) |
| 23 | Cherry-pick Ziyang's 31 commits (286e17a8c..ac2e5266e; closure 56 files, aggregate union) | — | LAST, after 22 |

Priority order (owner, 2026-09-26): C first (C3a–c, C4, S chain), then entry 22, then entry 23.

