# ACC9 acceptance log

- 2026-09-26T17:10Z start: base 481017246 (branch `codex/pc-target-c-psf`, build dir
  `E:\differential-geometry-pc3-lake` via the `.lake` junction).
- Accept list (19 new modules; lane logs DONE):
  - R0 (3): `Geometry/Metric/Sphere/Quotient/SimplyConnectedSpaceForm`, `Geometry/Metric/Sphere/Round/BallVolumeBound`
    (keeps ACC8's private copy of `det_le_of_quad_le`; `MetricComparison.lean` is at HEAD),
    `Perelman/CanonicalNeighborhood/SpatialRoundComponentVolume`.
  - NC0 (1): `Perelman/Noncollapsing/TerminalTime`.
  - C2W1 (3): `Analysis/Integration/Measure/Parametric/InjectiveAreaInequality`,
    `Perelman/LGeometry/Jacobian/MetricGaussianTail`, `Surgery/Topology/HistoryLGeometry/SeamBase`.
  - X (1): `Surgery/Topology/HistoryHorizonExtension`; primed `mem_Icc_of_mem_stageDomain'` renamed
    `mem_Icc_zero_horizon_of_mem_stageDomain` (conclusion `T ∈ Icc 0 H.horizon`; no clash, no in-tree
    user; DESIGN_C2_ASSEMBLY §5.4/§5.5 still spells the primed name — consumers must use the new one).
  - B6G2 (3): `Geometry/Metric/Pullback/LocalDistance`, `Surgery/Topology/NeckAlternativesLocalPull`,
    `Surgery/Topology/TracedRegionAncientLimitNeckAlternatives`.
  - BS1 (6): `Surgery/Topology/{CapWindowPointTimeSlack, SlabTimeWindowContinuity, SliverWindowData,
    SliceBallBoundTransfer, BoundedCurvatureAtDistanceSliver, InitialSlabScalarWindow}`.
  - C2E (2): `Perelman/LGeometry/Geodesic/ClosedStartVelocity`,
    `Surgery/Topology/HistoryLGeometry/ExponentialClosedStart` (first separate-module compile is this build).
- Exclude list (running lanes, left unstaged): H7B (`HistoryLGeometry/JacobianMonotone`, if present);
  C2M `HistoryLGeometry/{CostSemicontinuity, CurveAction, MinDomainMeasurable}`; B6G3 (all files:
  `Estimates/{LocalMetricTimeLipschitz, UniformMetricTimeLipschitz}`,
  `Metric/Convergence/CovariantDerivative/Norm/ManifoldUniformComparison`,
  `Surgery/Topology/TracedRegionAncientLimitTimeControl`); B6G4 `AncientPointedFlowLimitShiftedTransfer`;
  BS6 `BoundedCurvatureAtDistanceAfterEvent{,Capture,Pullback}`; SS1 `Comparison/Volume/Bishop/LocalBallRatio`,
  `SpatialRoundComponentBallVolume`, `BackwardTraceDistortionThreshold`, `CapWindowPointScalar`,
  `StageBallVolumeRatio`, `StageComponentSimplyConnected`; C4B1 `LocalPullScalarGradient`; C4B2
  `SpatialCanonicalWitness{BallVolume,Margins}`; C9 (`CoreIntegralBound`, if present); B13 design; logs of
  H7B, C2M, B6G3, B6G4, BS6, SS1, C9, C4B1.
- Closure of the 19 targets (`closure.py`): every other module is committed and unmodified; 11 leaves.
- Root aggregate: each module inserted after its last alphabetically smaller sibling in the same folder.
- Pre-build tracked edits: only `DifferentialGeometry.lean` and `ACC8_LOG.md`.
- 17:11:31Z build1 started: one hash-based call `LEAN_NUM_THREADS=3 lake build` with the 19 targets; subshell winpid 33060, lake.exe PID 39224 (child 46704).
- build1: `NeckAlternativesLocalPull` failed after 9.4 s with `std::bad_alloc` (host memory: four worker lean.exe of 4 GB each were running); no source error. Build continues; the same call is re-run once after it exits.
- build1 17:11:31Z-17:15:27Z exit 1: 15 accepted modules built with no output; 3 host failures, no source error: `NeckAlternativesLocalPull` bad_alloc, `SliverWindowData` and `InitialSlabScalarWindow` `failed to read file …Mathlib…olean.private` (files intact, dated 09-04; free RAM 3.7 GB at the time). build2 = the same 19-target call.
- build2 17:15:43Z-17:17:08Z (subshell winpid 35496) exit 0, 19342 jobs, 4 rebuilt (the 3 failed + `TracedRegionAncientLimitNeckAlternatives`); output: none besides progress. Rebuilt across build1+build2: exactly the 19 accepted modules, no committed module. Zero errors, warnings, info.
- audit (`AuditAcc9.lean` outside the tree, `lake env lean`, 3 threads, 17:17:19Z-17:31:25Z) exit 0:
  124 declarations of 19 modules, 0 failures; 52 public theorems, all [propext, Classical.choice,
  Quot.sound], no `sorryAx`; 13 linters (Mathlib standard set minus docBlame/docBlameThm) clean.
  Headlines foundational: `SpatialRoundComponent.volume_lower_of_simplyConnected`,
  `exists_isometry_round_sphere_of_constant_positive_sectional_curvature`,
  `parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt`, `lintegral_paramDensity_mul_le_lintegral_image`,
  `exists_uniform_tail_gaussian_metric`, `injOn_historyLExp_of_lt_of_mem_Ico`, `exists_extendHorizon_gt`,
  `reducedVolume_extendHorizon`, `exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain`,
  `exists_neckAlternatives_of_survivor_maps`, `…_not_capWindowPoint_{event,terminal}_of_sliver`.
- Source audit: no sorry/admit/axiom/nolint/heartbeat or diagnostic commands; no comments or docstrings;
  `set_option autoImplicit false`, no header (tree convention); `git diff --check` clean; two 101-char
  lines in `SliverWindowData` (the lakefile disables `linter.style.longLine`; left). `open private` in C2E's
  `ExponentialClosedStart` (H1/H3 helpers, as `ExponentialFamily`). Name search: the 52 public names have
  no short-name twin elsewhere in the tree.
- Kept as the lanes delivered: X's anonymous `(_ : H.horizon < T')`, `(_ : G.flow.base.metric … = …)`
  binders in `exists_extendHorizon_gt` (named ones trip the unused-variables linter; elaborated type
  identical); B6G2's three `(_ : …)` binders in `exists_neckAlternatives_of_survivor_maps` (same reason).
- Deferred merges/moves for the lead (not done; running lanes import or copy these files):
  promote `det_le_of_quad_le` in `MetricComparison` to public and drop `BallVolumeBound`'s private copy
  (still pending, next leaf-closure full build); C2W1's recast of `lSourceGaussian_uniform_tail` through
  `exists_uniform_tail_gaussian_metric_of_finrank_eq` (body given in `OPUS_FILL_LOG_C2W1.md`); SeamBase's
  copied privates (`eqOn_of_truncate_eq`, `mem_stageDomain_of_le_of_lt`, `lt_stageEndTime_of_lt'`, …) and
  the `Ioo` MinDomain/Truncation lemmas as corollaries of the `_of_mem_Ico` forms; C2E's private copy of
  `exists_chart_inner_bounds_on_compact`; `CapWindowPoint.of_le_time` next to `CapWindowPoint`
  (`CanonicalNeighborhoodContinuationLeaves.lean`); the generic compact-tube time-continuity helper of
  `SlabTimeWindowContinuity` belongs in `Topology/`; STRUCTURE.md: the `n`-sphere volume bound and the
  space-form isometry are correctly placed; R0a's `RoundSphereThree` specialisation stays in the flow file.
- Commits: e87e6d62f (R0 + NC0), 2c47e2482 (C2 wave 1 C2W1 + X + E), adc86324c (base slice BS1–BS5/BS7 + B6d glue B4–B6); root lines staged per group. Commit 4: designs, digests, finished-lane logs, ledgers.
- Commit 4 = 1640a9e11; pushed 481017246..1640a9e11 to liao/codex/pc-target-c-psf. This line left uncommitted.
