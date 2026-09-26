# ACC11 acceptance log

- 2026-09-26 start: base 88a4eec5a (branch `codex/pc-target-c-psf`, build dir
  `E:\differential-geometry-pc3-lake` via the `.lake` junction). Pipeline as ACC10 (scripts in the
  session scratchpad `acc11/`, outside the tree).
- Accept list (14 new modules; lane logs DONE):
  - B6G5 (1): `Surgery/Topology/TracedRegionAncientLimitScalarBound` (B13 composed headline).
  - C4B2 (5): `Perelman/CanonicalNeighborhood/{SpatialCanonicalWitnessMargins, SpatialCanonicalWitnessUniformTransport}`,
    `Perelman/StandardSolution/{StandardSpatialCanonicalMargins, StandardWindowBallPlacement, StandardWindowSpatialCanonical}`
    (no renames: C4B3 imports them).
  - C2M (3): `Surgery/Topology/HistoryLGeometry/{CostSemicontinuity, CurveAction, MinDomainMeasurable}`.
  - CP1 (5, new files cherry-picked from `origin/codex/pc-sorry-free` ebefde69b, c569a9285, 514704634;
    authors Bennett Chow, Ziyang Qin): `Geometry/Comparison/Volume/Bishop/CompactBallRatio`,
    `Geometry/Metric/Distance/CompactMinimizerInwardPoint`,
    `Surgery/Topology/{HistoryParabolicBallCrossing, MetricCutCapRegularCrossing, HistoryBallVolume}`.
  - Root-aggregate fix: committed `Perelman/CanonicalNeighborhood/CapCoreCylinderAbsorption` (ACC10 finding).
- Exclude list (running lanes, left unstaged): H7B (`HistoryLGeometry/{ActionSplit, AdaptedFieldIcc,
  AntitoneOffFinite, FamilyChain*, Jacobian*}`), SS2 (`HistoryNoncollapsingSliceTransfer`,
  `InitialLayerNoncollapsing`), SS3 (`SmallScaleNoncollapsingThroughSurgery`, `InitialWindowScalarBound`),
  C4B3, XA1, SA1; logs of H7B, SS2, SS3, C4B3, XA1.
- Closure (`closure.py`) of the 14 targets + CapCoreCylinderAbsorption: every other module is committed,
  unmodified and registered; leaves: StandardWindowSpatialCanonical, HistoryBallVolume, MinDomainMeasurable,
  HistoryParabolicBallCrossing, TracedRegionAncientLimitScalarBound, CapCoreCylinderAbsorption.
  The committed `Geometry/Comparison/Volume/CompactSmallBall` (imported by HistoryBallVolume) has no olean in
  the shared build; it is built as a dependency of the target (allowed).
- Source scan: no sorry/admit/axiom/nolint/option overrides/diagnostic commands, no comments or docstrings;
  `set_option autoImplicit false` only; lines > 100 chars in 13 files (lakefile disables
  `linter.style.longLine`; left); all 14 files have CRLF working-copy endings (autocrlf normalises on add).
  `open private`: B6G5 (three TracedRegionAncientLimit lemmas), C4B2 StandardSpatialCanonicalMargins (three
  StandardSliceSpatialCanonical helpers), C2M CurveAction / MinDomainMeasurable (E-lane and stage helpers).
- Root aggregate: each module inserted after its last alphabetically smaller sibling in the same folder
  (flat aggregate, import order irrelevant; B6G5's "after TimeControl/ShiftedTransfer" is satisfied since
  both are committed and registered).
- Pre-build tracked edits: only `DifferentialGeometry.lean` and `ACC10_LOG.md`.
- 18:18:08Z build1 started: one hash-based call `LEAN_NUM_THREADS=3 lake build` with the 15 targets; subshell winpid 1212, lake.exe PID 32144 (child 28524).
- build1 18:18:08Z-18:22:04Z exit 0, 19252 jobs; 16 compiles: the 14 accepted modules plus two committed, unmodified, registered modules that had no olean in the shared build (`Geometry/Comparison/Volume/CompactSmallBall`, expected, and `Estimates/LocalDistanceComparison`, both imported by HistoryBallVolume); CapCoreCylinderAbsorption was up to date. Output none besides progress: zero errors, warnings, info. No host failure, no rerun.
- Lead note (SS2): the shared build lacked oleans for the committed `CompactSmallBall`, `Estimates/InitialVolume`,
  `Surgery/Topology/InitialVolume`. build1 built `CompactSmallBall` and `Estimates/LocalDistanceComparison`
  (the latter also committed and olean-less) as dependencies of HistoryBallVolume; no other committed module
  was rebuilt. The two `InitialVolume` modules are not in this closure and were not built.
- audit1 (`AuditAcc11.lean` outside the tree, `lake env lean`, 3 threads, ~18:23Z-18:32:56Z) exit 0:
  127 declarations of the 15 modules, 0 failures (13 linters, no non-foundational axiom); 32 public theorems,
  all [propext, Classical.choice, Quot.sound], no `sorryAx`. No repair needed.
- Name search (`names.py`): 31 public names; only same-short-name hits are dot-API
  `SpatialCanonicalWitness.HasMargins.enlarge_constants` vs other structures' `enlarge_constants` (distinct
  full names). C4B2's M4 neck lemma is `SpatialNeck.exists_scale_invariant_transport_tolerance`, no clash with
  the committed `SpatialNeck.exists_uniform_transport_tolerance` (T2's clash note is stale).
  `git diff --check` clean; no trailing whitespace in the new files.
- LEAD: DROP CP1 (owner ordered the full cherry-pick of entry 23, which brings those files in their original
  form). The five CP1 import lines were removed from the root aggregate; the five CP1 files and
  `OPUS_FILL_LOG_CP1.md` are left untracked, not staged, not committed (their oleans in the shared build are
  to be ignored; build/audit results above covered them and were clean). Accepted: 9 modules + the
  CapCoreCylinderAbsorption root line.
- Headlines: `ObservedHistory.exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before` (B13),
  `ObservedHistory.upperSemicontinuous_regularizedCost` (M1), `…historyLCurve` AC/integrability/action (M3),
  `ObservedHistory.measurableSet_historyMinDomain{,_of_mem_Ioo}` (M),
  `StandardSolution.exists_spatialCanonicalWitness_with_margins` (M1a), `StandardSolution.exists_{,window_}ball_placement`
  (M1b), `SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance` (M4),
  `exists_window_spatialCanonicalWitness_of_standard_close` (M4★).
- Deferred merges for the lead (not done; running lanes import these files): B6G5: make public
  `scaleMetric_restrictOpen`, `mem_Icc_of_mem_window`, `isCompact_riemannianClosedBallOf_restrictOpen`
  (`TracedRegionAncientLimit`) and drop the `open private`; the copied pinching step of TimeControl. C2M: make
  public `isLRegularizedGeodesicOn_stage_of_isHistoryLGeodesicOn` (ExponentialClosedStart),
  `exists_lRegularizedSpeedSq_le_of_closedStart` (ClosedStartVelocity), `ExponentialSmooth`'s
  `mem_regularizedStage_{Icc,Ioo}`, `eq_of_mem_Ioo_of_mem_Icc`, `LWindow.mem_range_of_mem_Icc`, and CurveAction's
  `stageRegularizedLagrangian_congr_of_eventuallyEq` (used by MinDomainMeasurable via `open private`). C4B2:
  derive `exists_uniform_spatialNeck_canonicalWitness` and the private tip producer from the margin versions;
  private copies of `nonempty_window_tangentOrientation` (CanonicalWitnessPositiveAge) and
  `le_mul_of_half_scalar_lower` (CapWindowContinuationAssembly); `open private` of three
  StandardSliceSpatialCanonical helpers; `SpatialNeck.exists_scale_invariant_transport_tolerance` sibling of the
  committed `SpatialNeck.exists_uniform_transport_tolerance`.
- Commits: 2355d94f1 (Crossing B13, B6G5), e3d854792 (C4 (B) C4B2), 2431db7da (C2 M, C2M), 3163aea8e (root line for CapCoreCylinderAbsorption); root lines staged per group. CP1 not committed. Commit 5: designs, H13 digest, finished-lane logs (B6G5, C4B2, C2M, T2 retired), ledgers (FREE_INPUTS ACC11 section and S row, FILL_QUEUE C2/Crossing/S/C4/merges rows, HANDOFF_C ACC11 status, HANDOFF_S ACC11 update).
- Commit 5 = e68bf6466; pushed 88a4eec5a..e68bf6466 to liao/codex/pc-target-c-psf. This line left uncommitted.
