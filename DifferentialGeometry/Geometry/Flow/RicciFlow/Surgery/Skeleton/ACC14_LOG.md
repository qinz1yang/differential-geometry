# ACC14 acceptance log — C2c and C3c leaf closures (ILBB, X7) + XP2′ and SC7 bricks

- 2026-09-26T23:06Z start: base 6eb8d9343 (branch `codex/pc-target-c-psf`, build dir `E:\differential-geometry-pc3-lake`,
  ACC14 the only lake user). Pipeline as ACC13 (scripts copied to the session scratchpad `acc14/`, outside the tree).
  Tracked edits at start: only `ACC13_LOG.md` (its push line). Accept list (40 modules; lists `acc14/g{A..E}.txt`):
  - gA XP2′ (7): `Perelman/CanonicalNeighborhood/WindowScalarBoundNeckAlternatives`, `Surgery/Topology/{LocalFlowLimitWindowTransfer,
    AncientPointedFlowLimitWindowNeckAlternatives, CrossingMaximalWindow, NeckAlternativesLocalPullCompact,
    TracedRegionNeckAlternativesCompact, CrossingWindowAnchorBound}`.
  - gB X7 (1) + C3c skeleton edit: `Surgery/Topology/CrossingContinuationLeaf`.
  - gC ILBB relocation (20, from `origin/codex/wt17-pc-build-warning`, Bennett Chow).
  - gD ILBB own (4) + C2c skeleton edit: `Surgery/Topology/{CapWindowActionRegularCrossingRecenter, InitialEndpointPerturbation,
    InitialSpatialMinimum, InitialRegularBlock}`.
  - gE SC7 (8): `Perelman/CanonicalNeighborhood/InverseSqrtScalarDistance`, `Surgery/Topology/{TerminalCoreFrontierDistance,
    BoundedCurvatureAtDistanceBackwardTraces, HornChainBackwardTraces, HornTerminalScalarBound,
    RetainedCoreHistoryExtendAtTransport}`, `Topology/Sequences/{DiagonalChoice, RescalingFactor}`.
- Excluded (running lanes SX, SC8, T4A; left unstaged, 14 untracked Lean files): `LocalPullProductNeck`,
  `AncientLimitSurvivorCanonicalWitness`, `CrossingAncientLimitSpatial`, `HistoryPinchingOfCutoffRecords`,
  `HistoryStrongNeckStaggeredDepthInduction`, `HistoryStrongNeckTopSliceTracedRegion`, `HornPointSliceGeometry`,
  `RetainedCoreHistoryExtendAtLimitInputs`, `RetainedCoreHistoryExtendAtStageTransfer`, `ScaledPointedLimitLine`,
  `TracedRegionTimeZeroUniformBound`, `TracedRegionWindowLimit`, `TracedRegionWindowProductNeck`,
  `Geometry/Metric/Distance/SeparatedSideBallClause`. I29 and SL2's skeleton edit not applied.
- Closure per commit prefix (`closure.py`, accepted = earlier groups): every imported module outside the prefix is committed,
  unmodified and registered; no group depends on an excluded or running-lane file. Leaves: gA `CrossingWindowAnchorBound`,
  gB `CrossingContinuationLeaf`, gC `HistoryAction.MinimumPropagation`, gD `InitialRegularBlock`, gE 5.
- Source scan (`scan.py`, 40 files): no sorry/admit/axiom/nolint/option overrides/diagnostic commands/comments/docstrings;
  one `diag2` hit is the false positive `htrace.congr` (WithinSmoothnessScalar:52); lines > 100 chars only in ILBB's files
  (`longLine` off in the lakefile); CRLF working copies (12) normalised by autocrlf on add. `open private` in
  `LocalFlowLimitWindowTransfer` (1), `CrossingWindowAnchorBound` (1), `CapWindowActionRegularCrossingRecenter` (2), as the
  lane logs record.
- Names (`names.py`): 87 public declaration names, no duplicate within the set, no short-name coincidence with any other file
  on disk (ILBB's two renamed `covDerivAlong_map_localIso_of_mdifferentiableAt`,
  `covDerivAlong_map_of_local_isometry_on_of_mdifferentiableAt` present). The build is the full-name clash check.
- Edits: root aggregate +40 lines (`register.py`); skeleton: imports `CrossingContinuationLeaf`, `InitialRegularBlock`,
  `crossingContinuation := crossingContinuation_holds P₀ g₀` (X7 text), `historyReducedVolumeInitialLowerBound :=
  historyReducedVolumeInitialLowerBound_holds P₀ g₀` (ILBB text). Skeleton `sorry` 4 → 2 (S `uniformDebitSurgeryStepStrong`,
  C4 `spatialCanonicalContinuation`). Tracked edits now: root aggregate, `PoincareEndgame.lean`, `ACC13_LOG.md`.
- 2026-09-26T23:08:43Z build1 started: ONE call `LEAN_NUM_THREADS=4 lake build <40 accepted modules> …Skeleton.PoincareEndgame` (targets `acc14/targets1.txt`); not the root aggregate.
- 23:16:39Z build1 exit 0 ('Build completed successfully (19735 jobs)'), no retry needed: 42 compiles = the 40 accepted
  modules + the committed `Surgery/Topology/HistoryPoleAction` (no olean in the shared build; built as a dependency, 26 s,
  as ILBB recorded) + `PoincareEndgame` (19 s). Diagnostics: only the two expected `declaration uses 'sorry'` warnings of
  PoincareEndgame (:23 S `uniformDebitSurgeryStepStrong`, :60 C4 `spatialCanonicalContinuation`); zero errors, zero other
  warnings or infos. Wall time 23:08:43Z–23:16:39Z (~8 min; longest `HistoryAction.Index` 104 s).
- 23:17:03Z audit1 started (`acc14/AuditAcc14.lean` outside the tree, `lake env lean`, 4 threads).
- audit1 (23:17:03Z–23:39:54Z) exit 0: "audited 208+11 declarations; failures 0". Every declaration of the 40 modules: axioms
  within {propext, Classical.choice, Quot.sound}, no `sorryAx`; 85 public theorems printed, all
  `[propext, Classical.choice, Quot.sound]`; the 13 standard linters (docBlame/docBlameThm excluded) over these plus the 11
  lint-only declarations of `PoincareEndgame`: 0 findings (no unused-binder repair needed).
  Exact axiom lists: `crossingContinuation_holds` `[propext, Classical.choice, Quot.sound]`;
  `historyReducedVolumeInitialLowerBound_holds` `[propext, Classical.choice, Quot.sound]`;
  `smoothPoincareConjecture_holds` `[propext, sorryAx, Classical.choice, Quot.sound]`. Skeleton theorems now sorry-free:
  `crossingContinuation`, `historyReducedVolumeInitialLowerBound`, `noncollapsingThroughSurgery`,
  `canonicalNeighborhoodContinuation` (with the C2a/C2b/C2d ones); `sorryAx` only through `uniformDebitSurgeryStepStrong`
  (S) and `spatialCanonicalContinuation` (C4) and their consumers `canonicalNeighborhoodsThroughSurgeryStrong`,
  `smoothPoincareConjecture_holds`.
- `git diff --check` clean (tracked edits; `--no-index` check of the 40 new files: clean).
- Ledgers (`acc14/ledgers.py`): FILL_QUEUE (leaves list: two; 24b + C2c CLOSED; ACC14 paragraph: C2c/C3c CLOSED, XP2′,
  X7, ILBB, SC7 accepted; running lanes SX (SX + strong SX), SC8, T4A), FREE_INPUTS (leaf count two; section
  "Accepted 2026-09-26 (ACC14)"), HANDOFF_C (ACC14 update).
- Deferred merges recorded by the lanes (not done here): XP2′'s private copy `closedBall_one_subset_of_ball_eq_window` of
  XA4's `closedBall_one_subset_of_ball_eq`; ILBB's `covDerivAlong_map_localIso_of_mdifferentiableAt`,
  `covDerivAlong_map_of_local_isometry_on_of_mdifferentiableAt` generalize the committed lemmas; ILBA's
  `_of_derivative_before` chain becomes a corollary of ILBB's `_of_recenter_budget` chain; `open private` in
  `LocalFlowLimitWindowTransfer`, `CrossingWindowAnchorBound`, `CapWindowActionRegularCrossingRecenter`.
- Commits (each stages its files by path; root lines via `stageroot.py`; the Crossing closure commit carries the skeleton
  blob with the C3c edit only, the C2c edit goes with gD): f066d83a2 Crossing X4 bricks (XP2′, 7); efdf07d06 Crossing leaf
  closure (X7 + skeleton; 4 → 3 sorry); 2d7699c4d collaborator relocation (ILBB, 20; message line "relocated as new files
  from origin/codex/wt17-pc-build-warning; author Bennett Chow (commits e033fb1f3 01a76daf7 bd0be72d1 and their
  dependencies; declaration closure of exists_spatial_regularizedCost_minimum_lt_three_mul at 4c2e5c83b)"); b4f683085 C2c
  bricks + leaf closure (ILBB own 4 + skeleton; 3 → 2 sorry); 05de6202f S consumer wave 7 (SC7, 8).
- Docs commit: HANDOFF_20260927, finished lane logs XP2 (final), X7, ILBB, SC7, ACC13_LOG (push line), ACC14_LOG, ledgers
  FILL_QUEUE, FREE_INPUTS, HANDOFF_C. Left untracked (running lanes): OPUS_FILL_LOG_{SC8, SX, T4A}.md, WATCH_{SC8, SX,
  T4A}.md and the 14 excluded Lean files. CP2_LOG was already committed and unmodified.
