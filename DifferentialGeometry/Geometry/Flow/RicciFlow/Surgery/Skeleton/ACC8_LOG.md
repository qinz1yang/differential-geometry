# ACC8 acceptance log

- 2026-09-26T16:26Z start: base 9126abc30 (branch `codex/pc-target-c-psf`, build dir
  `D:\differential-geometry-pc3-lake\build` via the `.lake\build` junction).
- Accept list (21 new modules, all lane logs DONE):
  - B3F (12): `Surgery/Topology/{BackwardTraceChainCapture, BoundedCurvatureAtDistanceTracedLimit,
    BoundedCurvatureAtDistanceTracedCone, ConeEndRayScalarBound, BoundedCurvatureAtDistanceChainBuffers,
    BoundedCurvatureAtDistanceTracedSecondLevel, BoundedCurvatureAtDistanceTracedPositive,
    BoundedCurvatureAtDistanceSlice, BoundedCurvatureAtDistanceSliceTerminal, RetainedCoreHistoryPrefix,
    RetainedCoreHistoryPrefixTransport, BoundedCurvatureAtDistanceSliceEvent}`. `CanonicalCapScalar`
    and `TracedTerminalCompactness` (named in the brief) are committed and unmodified.
  - CF (1): `Surgery/Topology/HistoryParabolicBallForwardFlow`.
  - B6G1 (5): `Topology/Sequences/ExceptionalSetApproximation`, `Estimates/RicciLowerMetricComparison`,
    `Geometry/Curvature/CurvatureOperator/RicciLowerBound`,
    `Perelman/CanonicalNeighborhood/PinchingRicciLowerBound`,
    `Surgery/Topology/TracedRegionAncientLimitDerivativeCutoff`.
  - B6D (1): `Surgery/Topology/AncientPointedFlowLimitTransfer` (the `…_of_slice_bounds` refactor of
    `AncientPointedFlowLimitBoundedCurvature` is already in 9126abc30). Headline hypothesis `hEreg`
    is unsatisfiable by the consumer; to be restated by B11.
  - B6B'' (1): `Surgery/Topology/TracedRegionAncientLimitWitnesses`.
  - H7C (1): `Surgery/Topology/HistoryLGeometry/JacobianLimit`.
- Exclude list (running lanes, left unstaged): C2W1 `Analysis/Integration/Measure/Parametric/
  InjectiveAreaInequality`; C2E `Perelman/LGeometry/Geodesic/ClosedStartVelocity`; R0
  `Perelman/CanonicalNeighborhood/SpatialRoundComponentVolume`, `Geometry/Metric/Sphere/Quotient/
  SimplyConnectedSpaceForm`, `Geometry/Metric/Sphere/Round/BallVolumeBound` and the edit of
  `Analysis/Integration/Measure/Riemannian/MetricComparison` (`det_le_of_quad_le` made public);
  in-flux C2M/H7B/X files `Surgery/Topology/HistoryLGeometry/{ActionContinuity, CostSemicontinuity}`,
  `Perelman/LGeometry/Jacobian/MetricGaussianTail` (all modified at 16:22–16:25Z); logs of H7B, C2M,
  C2E, C2W1.
- Closure of the 21 targets: the only modified/untracked module outside the accepted set is R0's
  `MetricComparison` (1212 of the 10488 closure modules depend on it). None of the accepted files uses
  `det_le_of_quad_le`. A hash-based build would recompile those 1212 modules under ten concurrent
  worker compiles; the build therefore uses `lake build --old` (rebuilds modified modules only, no
  transitive rebuild): the accepted modules compile against the committed tree plus that one-word
  visibility change. Recorded for the next acceptance: R0's lane pays the 1212-module rebuild.
- Root aggregate: `HistoryLGeometry.JacobianLimit` after `IndexChain`; the other 20 appended.
- 2026-09-26T16:28:35Z build1 started: one call `LEAN_NUM_THREADS=3 lake build --old` with the 21 modules as targets; lake PID 7836 (msys 186382). No `PoincareEndgame`, no full-tree build (owner directive).
- 16:31Z: `--old` does not stop the cascade (it compares mtimes; R0's `MetricComparison` olean was
  rewritten at 16:29Z, so its 1212 closure dependents are rebuilt). Not killed: the cascade is owed
  by any build of this tree while R0's edit is in the working copy (and by R0's own acceptance), so
  killing only defers it; the accepted modules cannot be built by `lake build` without it. Estimated
  ~2.5 h at 3 threads. Workers compiling with `lake env lean` keep their loaded oleans.
- 16:33:38Z lead decision (no long builds outside leaf closures): build1 killed (`taskkill /PID 7836
  /T /F`; six processes of that tree; no lean.exe of mine left) after 31 rebuilt modules of the
  cascade. `MetricComparison.lean` restored to HEAD (`git checkout --`). R0's only consumer,
  `Geometry/Metric/Sphere/Round/BallVolumeBound.lean`, now carries a private copy of the
  `MatrixDet` section (`det_le_of_quad_le` and its three private helpers, local `open Matrix`,
  `open scoped MatrixOrder`) and calls it unqualified; read-only compile
  (`LEAN_NUM_THREADS=2 lake env lean`, lakefile options) 29 s, no output. R0 is NOT accepted here.
  Deferred merge: promote `det_le_of_quad_le` to public in `MetricComparison` and drop
  BallVolumeBound's private copy at the next leaf-closure full build.
- 16:34:46Z build2 misfire: the target file was missing, so `lake build` got no targets (default = full tree); killed after 7 s (PID 6100, tree), nothing built (log has no job line). Script now refuses an empty target list.
- 16:35:05Z build2 started: one hash-based call `LEAN_NUM_THREADS=3 lake build` with the 21 targets; lake PID 46784 (msys 188422).
- build2 16:35:05Z-16:44:31Z exit 1: 48 modules rebuilt, no source error; one host olean-read failure (`failed to read file …/LocalDiffeomorph/Descent.olean` while building the committed `BackwardTraceDistortion`; the olean is intact, unchanged since 04:18Z; same failure class as ACC5 build1). Re-running the same call (build3).
- 16:44:46Z build3 started (same 21 targets); lake PID 42708 (msys 190788).
  Correction: the recorded winpids (7836, 46784, 42708) are the background bash subshells that exec lake; build3's lake.exe is PID 41692 (child of 42708). `taskkill /T` on the subshell covers the lake tree.
- build3 16:44:46Z-16:49:33Z exit 0, 19194 jobs, 6 rebuilt; output: none besides progress. Rebuilt across build2+build3: 54 modules (17 accepted + 37 committed modules of the closure rebuilt once more after build1's MetricComparison olean); the other 4 accepted modules (B6G1's B1–B3, outside MetricComparison's cone) were built in build1 with no output and are up to date under the hash check. Zero errors, warnings, info.
- audit (`AuditAcc8.lean` outside the tree, `lake env lean`, 3 threads, 16:49:54Z-17:04:05Z) exit 0:
  152 declarations of 21 modules, 0 failures; 86 public theorems, all [propext, Classical.choice,
  Quot.sound]; 13 linters (Mathlib standard set minus docBlame/docBlameThm) clean. Headlines:
  `…_not_capWindowPoint_terminal`, `…_event`, `exists_common_flow_past_time_of_parabolicallyRmControlledBall`,
  `FiniteHorn.exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants`,
  `exists_pos_historyReducedJacobian_le_gaussian`, `abs_derivWithin_scalar_le_of_survivor_maps_of_lt`:
  foundational.
- Source audit: no sorry/admit/axiom/nolint/heartbeat or diagnostic commands; no comments or
  docstrings; `set_option autoImplicit false` and no header follow the `Surgery/Topology` convention;
  `open private` in B3F's `BackwardTraceChainCapture` (X2 helpers) and B6B'''s Witnesses (as in B5/X2b,
  already in the merges list). Name search: no clash (`RetainedCoreHistory.eventPrefix` vs a private
  root-level `eventPrefix` in `EventTimeNonaccumulation`; `CapWindowPoint.mono` unique).
- Deferred merges/moves for the lead (not done; running lanes import these files):
  `RetainedCoreHistory.CapWindowPoint.mono` belongs next to `CapWindowPoint`
  (`CanonicalNeighborhoodContinuationLeaves.lean`); the generic real-variable lemmas of
  `AncientPointedFlowLimitTransfer` (`abs_sub_le_mul_of_abs_deriv_le_of_finite`, the
  `…_of_finite` Harnack-type comparison family) belong in `Analysis/`, and its manifold helpers
  (`mfderiv_apply_mfderiv_symm_apply_of_mem_target`, `isometryOn_symm_of_isometryOn`,
  `exists_mem_connectedComponent_of_monotone_cover`) in `Topology/`/`Geometry/` homes; B6B'''s
  `SpatialCanonicalWitness.localPullOfInjective` belongs in `SpatialCanonicalWitnessTransport`;
  promote `det_le_of_quad_le` in `MetricComparison` to public and drop `BallVolumeBound`'s private
  copy at the next leaf-closure full build.
- Ledgers: FREE_INPUTS (ACC8 section), FILL_QUEUE (22 bricks, Crossing rows), HANDOFF_C (ACC8
  status), HANDOFF_S (B3e update).
- Commits: edc2b74b0 (B3e both slabs, 12 modules), fbd83ebcb (CF + H7c), eee792ac9 (B6d transfer, B6b'', B6d-glue B1–B3/B12); root lines staged per group. Commit 4: designs, digests, finished-lane logs, ledgers.
- Commit 4 = 481017246; pushed edc2b74b0..481017246 to liao/codex/pc-target-c-psf (9126abc30..481017246). This line left uncommitted.
