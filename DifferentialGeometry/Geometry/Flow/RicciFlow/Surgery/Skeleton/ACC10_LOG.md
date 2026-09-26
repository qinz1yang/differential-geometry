# ACC10 acceptance log

- 2026-09-26T17:35Z start: base 1640a9e11 (branch `codex/pc-target-c-psf`, build dir
  `E:\differential-geometry-pc3-lake` via the `.lake` junction). Pipeline as ACC9 (scripts in the
  session scratchpad `acc10/`, outside the tree).
- Accept list (23 new modules; lane logs DONE):
  - BS6 (3): `Surgery/Topology/BoundedCurvatureAtDistanceAfterEvent{Capture,Pullback,}`.
  - C9 (1): `Surgery/Topology/HistoryLGeometry/CoreIntegralBound`.
  - T5 (1): `Surgery/Contract/UniformDebitSurgeryStepOfFineCutNeckSupply` (`FineCutNeckSupply`,
    `uniformDebitSurgeryStepStrong_of_fineCutNeckSupply`).
  - B6G4 (1): `Surgery/Topology/AncientPointedFlowLimitShiftedTransfer` (B8–B11).
  - B6G3 (6): `Geometry/Metric/Convergence/CovariantDerivative/Norm/ManifoldUniformComparison`,
    `Estimates/{UniformMetricTimeLipschitz, LocalMetricTimeLipschitz}`,
    `Surgery/Topology/TracedRegionAncientLimitTimeControl`, `Perelman/Noncollapsing/EarlierTimeVolume`,
    `Surgery/Topology/AncientPointedFlowLimitTerminalNoncollapsing` (no renames: B6G5 imports them).
  - T1 (1): `Surgery/Topology/TerminalCapSideExclusion`.
  - SS1 (7): `Geometry/Comparison/Volume/Bishop/LocalBallRatio`, `Surgery/Topology/{StageComponentSimplyConnected,
    StageBallVolumeRatio, CapWindowPointScalar, BackwardTraceDistortionThreshold}`,
    `Perelman/CanonicalNeighborhood/{SpatialRoundComponentBallVolume, SpatialCanonicalWitnessBallVolume}`
    (no renames: SS3 imports them).
  - C4B1 (3): `Surgery/Topology/LocalPullScalarGradient`, `Perelman/StandardSolution/StandardWindowComparison`,
    `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniverseTransport` (no renames: C4B2 imports them).
- Exclude list (running lanes, left unstaged): H7B, C2M (`HistoryLGeometry/{CostSemicontinuity, CurveAction,
  MinDomainMeasurable}`), SS2/SS3 (`Surgery/Topology/InitialLayerNoncollapsing` if theirs), C4B2
  (`SpatialCanonicalWitness{Margins,UniformTransport}`, `StandardSolution/{StandardSpatialCanonicalMargins,
  StandardWindowBallPlacement}`), B6G5 (`TracedRegionAncientLimitScalarBound`), T2, DESIGN_CROSSING_ASSEMBLY,
  DESIGN_S_SUPPLY; logs of H7B, C2M, C4B2, B6G5 and any other running lane.
- Closure of the 23 targets (`closure.py`): every other module is committed and unmodified; 14 leaves. One
  committed closure module is not in the root aggregate: `Perelman/CanonicalNeighborhood/CapCoreCylinderAbsorption`
  (pre-existing; not touched here, reported to the lead).
- Source scan: no sorry/admit/axiom/nolint/option overrides/diagnostic commands, no comments or docstrings;
  `set_option autoImplicit false` only; lines > 100 chars in several files (lakefile disables
  `linter.style.longLine`; left); seven files have CRLF working-copy endings (autocrlf normalises on add).
  `open private` in T5 (UniformDebitSurgeryStepOfFactory helpers), B6G3's TimeControl and
  TerminalNoncollapsing (as Data.lean/Transfer).
- Root aggregate: each module inserted after its last alphabetically smaller sibling in the same folder
  (flat aggregate; SS1's dependency order is irrelevant to it).
- Pre-build tracked edits: only `DifferentialGeometry.lean` and `ACC9_LOG.md`.
- 17:35:27Z build1 started: one hash-based call `LEAN_NUM_THREADS=3 lake build` with the 23 targets; subshell winpid 38824, lake.exe PID 18960 (child 33928).
- build1 17:35:27Z-17:41:23Z exit 0, 19688 jobs; rebuilt exactly the 23 accepted modules (no committed module), output none besides progress. Zero errors, warnings, info. No host failure, no rerun.
- audit1 (`AuditAcc10.lean` outside the tree, `lake env lean`, 3 threads, 17:41:30Z-17:54:42Z) exit 1:
  147 declarations of 23 modules, 2 failures, both `unusedArguments` on C4B1's PRIVATE
  `capCore_transport_of_partialDiffeomorph_lift` and `positiveComponent_transport_of_partialDiffeomorph_lift`
  (`SpatialCanonicalWitnessUniverseTransport`): unused `[IsManifold I3 ∞ P]`, `[IsManifold I3 ∞ M]`. Repair:
  the four instance binders removed (private, no API change; C4B2's imports unaffected). 47 public theorems,
  all [propext, Classical.choice, Quot.sound], no `sorryAx`; the other 11 linters clean on all 147.
- 17:55:20Z build2 (one target, the repaired module; subshell winpid 34696) exit 0 at 17:56:42Z, 1 rebuilt,
  no output. audit2 (that module, 48 declarations, 13 linters + axioms): 0 failures.
  Total: 24 module compiles across 2 builds (23 accepted modules, one twice), no committed module rebuilt.
- Name search (`names.py`): the 49 public names of the 23 files have no short-name twin elsewhere in the tree.
  `git diff --check` clean; no trailing whitespace in the new files.
- Headlines (foundational): `…exists_scalar_bound_at_distance_of_not_capWindowPoint_after_event` (BS6),
  `exists_lintegral_image_historyMinDomain_core_le` (C9), `uniformDebitSurgeryStepStrong_of_fineCutNeckSupply`
  (T5), `TerminalCorePresentation.false_of_terminal_capSide` (T1),
  `exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants_of_time_lipschitz` (B11),
  `exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before` (B7-κ),
  `parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit_of_time_lt`,
  `exists_ball_volume_of_spatialCanonicalWitness{,_of_simplyConnected}` (S4/S4′),
  `…exists_isParabolicallyRmControlledBall_or_capWindowPoint_of_scalar_le` (S1),
  `StandardSolution.exists_window_metricComparisonOn{,_of_lt}` (M2), `…pushforwardOfInjectiveULift` (M3).
- Deferred merges/moves for the lead (not done; running lanes import these files):
  C4B1 M3: generalize `SpatialCanonicalWitnessTransport.lean` in place to universes `v`, `max u v`, then
  delete `SpatialCanonicalWitnessUniverseTransport.lean` (1132 lines of privately copied generalized chain)
  and rename `…ULift` back to `pushforwardOfInjective`; C4B1 M2's private copy of the
  `subtypeVal_symm_isometry` step. B6G3: generalize `exists_uniform_iterated_covariant_derivative_norm_comparison`,
  `exists_uniform_metric_deriv_norm_reference_bound`, `exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds`
  (and the private `exists_local_closed_metric_covariant_bounds`) in place to the M-universal forms and delete the
  clones; B6b′ (`TracedRegionAncientLimitData`) as a corollary of TimeControl's core; the copied B6c-κ core in
  `AncientPointedFlowLimitTerminalNoncollapsing`; NC0 as the δ→0 corollary of `EarlierTimeVolume`. B6G4: make
  `metricDerivNorm_localPullMetric_of_injective` public in `Metric/Convergence/DerivativeNorm/`; fourth copy of the
  `opensSigmaCompact…` local instance. BS6: private copy of `exists_window_point_of_edist_le`
  (BackwardTraceDistortion) — make the original public; `OrientedThreeStage.exists_first_touch_of_not_subset`
  belongs in `Geometry/Metric/Distance` once `closure_riemannianBallOf` moves below it. C9:
  `exists_mem_historyLExpDomain_eqOn_of_commonFlow` (private) generalizes JacobianLimit's
  `historyLCurve_eqOn_window`. T5: move into `UniformDebitSurgeryStepOfFactory` (drop `open private`,
  retire `_of_long_slabs`). T1: `horn_sides_of_complementPair` could call `positiveHornMap_injective`. SS1:
  re-derive `scalar_le_four_mul_max_of_gradient_bound` (`SlabGradientScalarControl`) from
  `scalar_le_four_mul_of_gradient_bound`.
- Pre-existing, not touched: committed `Perelman/CanonicalNeighborhood/CapCoreCylinderAbsorption` is not in the
  root aggregate.
- Ledgers: FREE_INPUTS (ACC10 section, S row), FILL_QUEUE (C2/small-scale, Crossing, S bricks, C4 rows),
  HANDOFF_C (ACC10 status), HANDOFF_S (H12 / B13 update).
- Commits: fc6a793cc (Crossing: BS6 + B6G3 B7 + B6G4 B8–B11), 756ec665a (C2 C9), d6b5d9076 (small-scale SS1), 356b319c2 (S: T5 + T1), 9d37f6e47 (C4 (B) C4B1); root lines staged per group. Commit 6: designs, digest, finished-lane logs, ledgers.
