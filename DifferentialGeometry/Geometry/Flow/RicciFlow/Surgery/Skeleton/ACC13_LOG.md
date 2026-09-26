# ACC13 acceptance log — C2 leaf closure (reduced-volume monotonicity and local upper bound) + brick acceptance

- 2026-09-26T20:10Z start: base e68bf6466 + ACC12's uncommitted leaf closure (branch `codex/pc-target-c-psf`,
  build dir `E:\differential-geometry-pc3-lake`). Pipeline as ACC10/ACC11/ACC12 (scripts in the session
  scratchpad `acc13/`, outside the tree). ACC12 build1 still running (lake PID from `acc12/pids.txt`):
  waiting for ACC12's push before touching the index or running lake.
- Accept list (56 modules, all lane logs DONE; scratch lists `acc13/g1..g6.txt`):
  - g1 C2 H7b (17): `Surgery/Topology/HistoryLGeometry/{AntitoneOffFinite, FamilyChain, FamilyChainSections,
    AdaptedFieldIcc, FamilyChainJacobi, FamilyChainTrace, FamilyChainGram, FamilyChainClosure, FamilyChainCover,
    FamilyChainExists, FamilyChainConjugate, ActionSplit, JacobianAlong, JacobianDerivative, JacobianSeam,
    JacobianEndpoint, JacobianMonotone}`.
  - g2 C2W (5): `HistoryLGeometry/{JacobianClosedStart, JacobianComparison, SeamBaseJacobian, JacobianGaussian,
    ReducedVolumeTail}`.
  - g3 C2L (2) + skeleton closure: `Surgery/Topology/{HistoryReducedVolumeMonotone, HistoryReducedVolumeLocalUpperBound}`.
  - g4 Crossing bricks (18): XA1 `Surgery/Topology/{InitialWindowScalarBound, TracedRegionMaximalDepth,
    AncientPointedFlowLimitBaseScalar}`, `Topology/Sequences/NestedSubsequence`, `Compactness/Limits/PointedLimitOrientation`;
    XP1 `Perelman/StandardSolution/StandardCloseComparison`, `Surgery/Topology/{CapWindowBallCapture,
    CrossingPersistenceInputs, SurvivorTraceScalar}`; XA2 `Surgery/Topology/{RetainedCoreHistoryExtendAt,
    RetainedCoreHistoryPrefixInvariants, CrossingBadPoint, CrossingClauseTransport}`,
    `Perelman/CanonicalNeighborhood/CanonicalWitnessTimeRestrict`; XA3 `Surgery/Topology/CrossingAncientLimit`;
    XP2 `Surgery/Topology/{CapWindowSliceComparison, BoundedCurvatureAtDistanceAnchor}`; XP4
    `Perelman/CanonicalNeighborhood/WindowScalarBound`.
  - g5 C4 bricks (3): C4B3 `Surgery/Topology/CapWindowSpatialCanonicalWitness` (M5); C4A
    `Surgery/Topology/{SpatialCrossingContinuation, SpatialCanonicalContinuationCases}` (I29 NOT applied).
  - g6 S bricks (11): SC1 `Topology/Connected/InteriorCollar`, `Surgery/Topology/{TerminalHornCanonicalNeck,
    HistoryStrongNeckTrigger}`, `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessNeckExclusion`; SP1
    `Perelman/CanonicalNeighborhood/{StrongNeckRestriction, TruncatedNeck}`, `Surgery/Topology/HistoryStrongNeck`;
    SP2 `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessFrontier`,
    `Perelman/StandardSolution/{StandardCapSpatialCanonical, StandardWindowCapWitness}`, `Surgery/Topology/CapWindowCapWitness`.
- Exclusions (running lanes, left unstaged): XA4, XP3, SC2, SC3 and their files; ACC12's own files are ACC12's.
- Closure (`closure.py`) of the 56 modules: every module outside the set is committed, unmodified and registered
  (no dependency on ACC12's or CP2's files, none on a running lane's file); 13 leaves.
- Source scan (`scan.py`): no sorry/admit/axiom/nolint/option overrides/diagnostic commands, no comments or
  docstrings, `set_option autoImplicit false` only, no trailing whitespace; lines > 100 chars only import /
  `open private` lines (one in JacobianClosedStart outside those, lakefile disables `longLine`); 15 files have
  CRLF working copies (autocrlf normalises on add). `open private` in 16 files (H7b, C2W, XA2 PrefixInvariants,
  XA3, SP2 StandardCapSpatialCanonical) as recorded in the lane logs.
- Names (`names.py`): 166 declaration names; short-name coincidences only dot-API (`TruncatedNeck.mono`,
  `….restrictOpen`, `….timeRestrict`, `DepthExtendable.{comp,congr,mono_depth}`) and H7b's recorded
  `LFamilyChain.energy` / `LFamilyChain.regular_of_mem_piece` (distinct full names). The root build is the
  full-name clash check.
- Skeleton patch prepared (`skel.py`, C2L log text verbatim): two imports after SmallScaleNoncollapsingThroughSurgery;
  `historyReducedVolumeMonotone P₀ := historyReducedVolumeMonotone_holds P₀`, same for `…LocalUpperBound`.
- Lead scope addition (20:35Z): g7 CP2 relocation, the 34 modules of `cp2/order.txt` (9 verbatim collaborator
  modules + 25 sibling files; log `CP2_LOG.md` records the relocation finished, all 34 compile clean), ONE commit
  with the provenance line; the committed `StandardCap/WindowDiscarding`, `Topology/CapWindowAction`,
  `Topology/HistoryActionJoin` have no olean in the shared build and are built as dependencies (recorded, allowed).
  g8 ILBA (24a): `Surgery/Topology/{CapWindowActionRegularCrossingBefore, RegularMinimizerEndpointBarrier}`
  (import CP2's `CapWindowActionRegularCrossing`). ILBB (24b) running: its files excluded.
- Closure of g7 (with g1–g6 accepted) and of g8 (with g1–g7): only committed, unmodified, registered modules outside
  the sets. Scan of g7/g8: clean (lines > 100 chars in the collaborator's text, `open private` in
  TerminalActionCompactness (11) and CapWindowActionRegularCrossingBefore (1)). Names (92 modules, 285
  declaration names): additionally `ClosedSlab.abs_derivWithin_scalar_le_of_forall_Ioo` (ILBA) vs the committed
  `IncomingSlab.…` twin (distinct namespaces); CP2's own clash check vs every file: none.

## Restart (ACC13, second dispatch), 2026-09-26T22:05Z
- The first ACC13 dispatch stopped before any build (ACC12's full build1 never finished; ACC12 unpushed). Owner
  directive now: NO full-tree build, one focused hash-based `lake build` of the explicit accepted modules +
  `…Surgery.Skeleton.PoincareEndgame`, `LEAN_NUM_THREADS=4`. ACC13 is the only lake user; the running lean.exe
  processes are worker lanes' read-only compiles.
- Base e68bf6466. Tracked edits: root aggregate (SS2/SS3 three lines), `PoincareEndgame.lean`,
  `CanonicalNeighborhoodsThroughSurgeryStrong.lean` (ACC12's), `ACC11_LOG.md`, `ANALYSIS_ILB.md` (ledger/log).
  The two Lean edits match `OPUS_FILL_LOG_SS3.md` "Interface edit list" route A item by item (`hcn` binders at
  :241/:256 gain `[SimplyConnectedSpace P₀.Carrier]`; skeleton import + leaf
  `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀`; instance binders on
  `noncollapsingThroughSurgery`, `canonicalNeighborhoodsThroughSurgeryStrong`; `smoothPoincareConjecture_holds`
  unchanged). No other tracked edit: nothing reverted.
- Scope extended to 135 modules in 12 commit groups (scratch `acc13/g*.txt`, order `all2.txt`):
  gS small-scale closure (SS2 2 + SS3 1); g1 H7b (17); g2 C2W (5); g3 C2L (2) + skeleton edit; g5 C4 (3);
  g4 Crossing A (XA1, XP1, XA2, XA3, XP2 finished part, XP4: 18); g9 Crossing B (XP3 4 + XA4 7);
  g6 S producers (SP1, SP2, SC1: 11); g10 S consumer waves (SC2 7, SC3 5, SC4 5, SC5 4, SC6 4); g11 S leaf
  structure (SL1 2, SL2 2; SL2's skeleton edit NOT applied); g7 CP2 relocation (34); g8 ILBA (2).
- Excluded (running lanes XP2′, SC7, SC8, X7, ILBB; left unstaged): `InverseSqrtScalarDistance`,
  `WindowScalarBoundNeckAlternatives`, `AncientPointedFlowLimitWindowNeckAlternatives`,
  `BoundedCurvatureAtDistanceBackwardTraces`, `CapWindowActionRegularCrossingRecenter`, `CrossingContinuationLeaf`,
  `CrossingMaximalWindow`, `CrossingWindowAnchorBound`, `HornChainBackwardTraces`, `InitialEndpointPerturbation`,
  `InitialRegularBlock`, `InitialSpatialMinimum`, `LocalFlowLimitWindowTransfer`, `NeckAlternativesLocalPullCompact`,
  `RetainedCoreHistoryExtendAtTransport`, `TerminalCoreFrontierDistance`, `TracedRegionNeckAlternativesCompact`,
  `Topology/Sequences/{DiagonalChoice, RescalingFactor}`.
- Closure per commit prefix (`closure.py`, accepted = earlier groups): every imported module outside the prefix is
  committed, unmodified and registered; g11 imports the edited `CanonicalNeighborhoodsThroughSurgeryStrong`
  (committed in the gS commit). No group depends on an excluded file.
- Source scan (`scan.py`, 135 files): no sorry/admit/axiom/nolint/option overrides/diagnostic commands; the only
  comment hits are the module docstrings `/-!` after the imports (XP3 ×3, XA4 ×3, OpenClosedGluing); the `diag2`
  hits are `….trace.…` field accesses / `…_trace.{u}` names (false positives of the `trace.` pattern); lines
  > 100 chars allowed (`longLine` off in the lakefile); CRLF working copies normalised by autocrlf on add.
- Names (`names.py`, 389 declaration names): no duplicate within the new set; exact written-name twins only the
  recorded `energy`, `regular_of_mem_piece` (H7b, `LFamilyChain.…`) and `abs_derivWithin_scalar_le_of_forall_Ioo`
  (ILBA `ClosedSlab.…` vs committed `IncomingSlab.…`); suffix twins are dot-API in distinct namespaces
  (`TruncatedNeck.{mono,restrictOpen,toSpatialNeck}`, `StrongNeck.{restrictOpen,timeRestrict}`,
  `CanonicalWitness.timeRestrict` vs `PointedFlowData`/`SolutionOn`/`CompleteBoundedCurvatureSolutionOn.timeRestrict`,
  `DepthExtendable.{comp,congr,mono_depth}`, `SpatialNeck.ofRestrictOpen`,
  `SpatialCanonicalWitness.exists_localNeck_of_product_chart` vs `CanonicalWitness.…`). No full-name clash.
- Edits: root aggregate +132 lines (`register.py`, alphabetical within folder; 135 new lines in total with ACC12's
  three); skeleton C2L edit applied (`skel.py`: two imports after SmallScaleNoncollapsingThroughSurgery,
  `historyReducedVolumeMonotone P₀ := historyReducedVolumeMonotone_holds P₀`, same for `…LocalUpperBound`).
  Skeleton `sorry` 6 → 4 (S `uniformDebitSurgeryStepStrong`, C2c `historyReducedVolumeInitialLowerBound`,
  C3c `canonicalNeighborhoodContinuation`, C4 `spatialCanonicalContinuation`).
- 2026-09-26T22:07:37Z build1 started: ONE call `LEAN_NUM_THREADS=4 lake build <135 accepted modules> …Skeleton.PoincareEndgame` (targets `acc13/targets1.txt`); not the root aggregate.
- 22:27:09Z build1 exit 1: 133 modules compiled, no Lean error or warning; the single failure is an olean read error in `HistoryLGeometry/SeamBaseJacobian` ('failed to read file …/Geometry/Exponential/Intrinsic/Geodesic/Continuity.olean'; the olean is present and unchanged since 09-25, host under memory pressure: bash fork failures at the same time). Its dependents were skipped. Retry once (build2), same target list.
- 22:32:46Z build2 exit 0 ('Build completed successfully (19974 jobs)'): 5 compiles (SeamBaseJacobian and its dependents, PoincareEndgame). Totals build1+build2: 137 compiles = the 135 accepted modules + committed prerequisites without oleans built as dependencies `Surgery/Topology/TracedRegionDepthInduction`, `DimensionThree/TerminalProductSplitting` (PoincareEndgame rebuilt, 19 s). Diagnostics: only the four expected `declaration uses 'sorry'` warnings of PoincareEndgame (:21 S, :33 C2c, :49 C3c, :58 C4); zero errors, zero other warnings or infos. Wall time 22:07:29Z–22:32:46Z (~25 min incl. the retry).
- audit1 (`acc13/AuditAcc13.lean` outside the tree, `lake env lean`, 4 threads, 22:33:00Z–22:54:36Z) exit 0:
  "audited 645+22 declarations; failures 0". Every declaration of the 135 modules: axioms within
  {propext, Classical.choice, Quot.sound}, no `sorryAx`; 364 public theorems printed, 363 with
  `[propext, Classical.choice, Quot.sound]`, `ObservedHistory.natCast_le_infty` with `[propext, Quot.sound]`;
  the 13 standard linters (docBlame/docBlameThm excluded) over these plus the 22 lint-only declarations of
  `CanonicalNeighborhoodsThroughSurgeryStrong` and `PoincareEndgame`: 0 findings (no unused-binder repair needed).
  Leaf headlines `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace`, `historyReducedVolumeMonotone_holds`,
  `historyReducedVolumeLocalUpperBound_holds`: `[propext, Classical.choice, Quot.sound]`; skeleton theorems
  `smallScaleNoncollapsingThroughSurgery`, `historyReducedVolumeMonotone`, `historyReducedVolumeLocalUpperBound`
  now sorry-free; `sorryAx` only through `uniformDebitSurgeryStepStrong`, `historyReducedVolumeInitialLowerBound`,
  `crossingContinuation`, `spatialCanonicalContinuation` (and their consumers `noncollapsingThroughSurgery`,
  `canonicalNeighborhoodContinuation`, `canonicalNeighborhoodsThroughSurgeryStrong`).
  `smoothPoincareConjecture_holds`: `[propext, sorryAx, Classical.choice, Quot.sound]`.
- `git diff --check` clean (tracked edits and every new file; only autocrlf notices).
- Ledgers (`ledgers.py`): FILL_QUEUE (leaves list: four; entry 22 CLOSED by H7b/C2W/C2L; 24a DONE, 24b running;
  entry 23 DONE by relocation; ACC13 paragraph with owner decisions A-lite, entry 23 by relocation, no full-tree
  builds on this host, and the running lanes XP2′/SC7/SC8/X7/ILBB), FREE_INPUTS (leaf count four; section
  "Accepted 2026-09-26 (ACC13)"), HANDOFF_C / HANDOFF_S (ACC13 updates).
- Commits (each stages its files by path; root lines via `stageroot.py`; the gS commit carries the skeleton
  blob with ACC12's edits only, bbcb57c81, the C2L edit goes with g3):
  3378522d8 small-scale closure (SS2, SS3, route A; skeleton 7 → 6 sorry);
  9c3ec5af8 C2 H7b (17); 0171972a1 C2 H7b+/SB3/Gauss/T9 (C2W, 5); 365052184 C2 leaves closure (C2L 2 +
  skeleton; 6 → 4 sorry); b1029b3dc C4 bricks (C4B3, C4A); 3ccf4e4f9 Crossing A (XA1, XP1, XA2, XA3, XP2
  finished part, XP4: 18); 3135b581e Crossing B (XP3 4, XA4 7); 845c9526a S producers (SP1, SP2, SC1: 11);
  d9106490c S consumer waves (SC2–SC6: 25); 63918ea71 S leaf structure (SL1, SL2: 4); 36e62dca3 CP2
  relocation (34, provenance line verbatim, authors Bennett Chow, Ziyang Qin); e531fb5e5 24a (ILBA, 2).
- Deferred merges recorded by the lanes (not done here): SS3's private general initial-layer form →
  public primary theorem in `InitialLayerNoncollapsing` (drop both private copies); SC5's three private copies
  of `rm04_eq_zero_of_image_finrank_eq_zero`; `open private` in H7b/C2W/XA2/XA3/SP2/XP3/XA4/CP2/ILBA files
  (their lane logs list the privates to make public in a quiet window).
- Docs commit: digests H14–H20, DESIGN_X4D / DESIGN_C4_ASSEMBLY / DESIGN_STRONG_INTERFACE, finished lane logs
  (H7B, C2W, C2L, C4B3, C4A, XA1, XP1, XA2, XA3, XA4, XP3, XP4, SS2, SS3, SP1, SP2, SC1–SC6, SL1, SL2, CP1, CP2,
  ILBA), ACC11_LOG, ACC12_LOG, ACC13_LOG, ANALYSIS_ILB, ledgers. Left untracked (running lanes): OPUS_FILL_LOG_{XP2,
  SC7, X7, ILBB}.md and the 19 excluded Lean files.
