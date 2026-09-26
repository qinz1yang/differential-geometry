# OPUS_FILL_LOG_SS3 — small-scale leaf: S7 case assembly and the leaf in premise form

Design: `Skeleton/DESIGN_SMALLSCALE.md` §2, §3 S7, §6.2, §6.6. Worktree `D:\differential-geometry-pc3`,
branch `codex/pc-target-c-psf`. New files only; no builds, no git writes. Scratch route:
`<session scratchpad>\ss3\scomp.sh` (uncommitted imports rewritten to root `SS3`, oleans emitted to
`ss3\olean`, lakefile options passed, 2 threads); `rcomp.sh` retries on transient
"failed to read file" (host memory pressure while ACC lanes build).

## 2026-09-26

- 17:32Z start. SS2 (S0-def/S0, S6) has no log or files yet.
- 17:34–17:38Z scratch oleans for the SS1 deliverables (LocalBallRatio, StageBallVolumeRatio,
  StageComponentSimplyConnected, CapWindowPointScalar, BackwardTraceDistortionThreshold; the two
  witness-volume files retried after transient read failures).
- S7 probe (with a local copy of the S0-def) compiles clean with a real body. Statement deviation:
  S7's binders `hr₀ : 0 < r₀` and `hr₀η : r₀ ^ 2 ≤ η` of the design are unused by the proof (the low
  case gets `0 < r₀` from `hlow`'s control; the early case needs only `r ≤ 1`) and would trip
  `unusedArguments`; dropped. Added `hκ₁ : 0 ≤ κ₁` and weakened `hcBG` to `0 ≤ cBG` (needed to split
  `ofReal (cBG * κ₁)`).

## 2026-09-26 (resumed lane, new worker)

- 18:17Z resume. On disk: `Surgery/Topology/SmallScaleNoncollapsingThroughSurgery.lean` (676 lines) with S7,
  the S1/S2 wrappers, the witness/slab-supply glue, the record-bound lemma, a private S6 twin
  (`exists_initial_layer_noncollapsed_of_initialIdentification`, uses SS2's closed-slab corollary), and
  the leaf in premise form plus an instance-binder twin; the tail was never compiled.
  `InitialWindowScalarBound.lean` is not SS3's (crossing-assembly lane). SS2 files on disk, no `sorry`.
- Scratch route moved to `<scratchpad>\ss3b` (root `SS3B`). Scratch oleans: `CompactSmallBall`,
  `Estimates/InitialVolume`, `Topology/InitialVolume` (committed, but their shared oleans are missing
  mid-cascade), SS2's `HistoryNoncollapsingSliceTransfer`, `InitialLayerNoncollapsing`. SS1 oleans are
  in the shared build.
- 18:20Z leaf switched to the instance-binder shape:
  `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace (P₀) [SimplyConnectedSpace P₀.Carrier]
  (g₀) : SmallScaleNoncollapsingThroughSurgery P₀ g₀`; the primed twin (a name with a prime) removed.
  The instance is used (R4 `simplyConnectedSpace_connectedComponent_stage` for `hsimply`).
- 18:21Z whole file compiles clean against the scratch oleans: 0 errors, 0 warnings, linter set on
  (671 lines). `#print axioms` for the leaf and for S7: `[propext, Classical.choice, Quot.sound]`.
- Skeleton-shape probe (removed): with the leaf, both
  `theorem _ (P₀) [SimplyConnectedSpace P₀.Carrier] (g₀) : SmallScaleNoncollapsingThroughSurgery P₀ g₀ :=
  smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀` and the premise form
  `(P₀) (g₀) : SimplyConnectedSpace P₀.Carrier → SmallScaleNoncollapsingThroughSurgery P₀ g₀ :=
  fun _ => smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀` elaborate, axioms clean.
- Route-A probe (removed): the whole endgame chain with the instance on the skeleton theorems and on
  the `hcn` binders (copies of `hext_…`/`smoothPoincareConjecture_of_…` with the new binder, other leaves
  `sorry`) elaborates: 0 errors, only the expected `sorry` warnings, no linter findings.

### Deviations
- S7: `hr₀`, `hr₀η` dropped (unused), `hκ₁ : 0 ≤ κ₁` added, `hcBG` weakened to `0 ≤ cBG` (earlier entry).
- Constants: `M := max (max qs (1/4)) (c²/η)` (not `max qs (1/4)`) so that `c²/M ≤ η` and the
  backward window of S1 stays in `[0, t]`; `r₀ := min (min ε (c/√M)) 1` (the `√η` cap is then implied);
  `c := 1/(4L)`, `L := 1 + Cgrad + 8Ctime + 3072(1+φ1+φ0)²`; S2 used with `Cw = 2` (SS1's form);
  `δmax := 1`, `ρmax := (√(4K))⁻¹`, `K := (2 + 16Ctime c²)M`; `εcap` from S2a and the cap-scalar lemma;
  `Dcap := Dcw + 2`, `mcap := 2`.
- S6: the class form `exists_initial_layer_noncollapsed` (SS2) cannot serve the terminal half: the
  extended history `H.extendHorizon T …` is not `InCutoffClass` (its last event time is not its
  horizon). The file therefore proves privately the general form
  `exists_initial_layer_noncollapsed_of_initialIdentification` (hypotheses: an initial identification
  and singular incoming endpoints; no `ρbound ≤ ρ₁`), with a private copy of SS2's
  `ObservedHistory.ball_volume_lower_bound_of_closedSlab_stage_zero`.
  **Deferred merge:** make the general form the public primary theorem in `InitialLayerNoncollapsing.lean`,
  derive SS2's class form from it, and drop both private copies from this file.

### Interface edit list (acceptance lane)
Recommended **route A** (no `def` changes; the instance sits on theorems where it is used):
1. `Surgery/Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:241` and `:256`: replace
   `(hcn : ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric),` by
   `(hcn : ∀ (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric),`.
   Bodies unchanged (`hext_…` already builds the instance before `hcn (ofClosedOrientedManifold …) g`).
2. `Surgery/Skeleton/PoincareEndgame.lean`: add
   `import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmallScaleNoncollapsingThroughSurgery`;
   `:34–36` becomes
   `theorem smallScaleNoncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier]`
   `    (g₀ : P₀.Metric) : SmallScaleNoncollapsingThroughSurgery P₀ g₀ :=`
   `  smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀`;
   `:38` `noncollapsingThroughSurgery` and `:57` `canonicalNeighborhoodsThroughSurgeryStrong` gain
   `[SimplyConnectedSpace P₀.Carrier]` after `(P₀ : OrientedThreeStage.{u})`; bodies unchanged;
   `:63` `smoothPoincareConjecture_holds` unchanged.
3. `DifferentialGeometry.lean`: register the new module (plus SS2's two modules).
Route B (§6.2 literal, premise in the `def`s): §6.2 items 1–5 as written, but item 6 must NOT add the
instance to `smallScaleNoncollapsingThroughSurgery`/`noncollapsingThroughSurgery` (it would be unused
there). Skeleton `:34–36` becomes `(P₀) (g₀) : SmallScaleNoncollapsingThroughSurgery P₀ g₀ :=
smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀`, and in
`Surgery/Topology/SmallScaleNoncollapsingThroughSurgery.lean:522–525` the leaf loses its binder
`[SimplyConnectedSpace P₀.Carrier]` and its proof starts `intro _ B ε …` instead of `intro B ε …`
(otherwise the old binder becomes unused). Route A needs no edit in this file.
