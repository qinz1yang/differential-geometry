# Lane CP2: cherry-pick of the collaborator's commits (FILL_QUEUE entry 23)

Paths relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/` unless absolute.
Scratch: session scratchpad `cp2/` (outside the tree).

## Plan / state
- 2026-09-26 start. pc3 HEAD 88a4eec5a; ACC11 in progress (build1 done, not yet pushed; it is committing the
  5 CP1 files).
- Source: `origin/codex/pc-sorry-free` = 514704634 (fetched); merge-base 286e17a8c; 41 commits
  (ca4585835 .. 514704634), authors Ziyang Qin, Bennett Chow.
- Preparation worktree `D:\differential-geometry-pc23`, branch `codex/pc-entry23` (own index, no build).
- Lead sequencing change: wait for ACC11's push AND then ACC12's push (`ACC12_LOG.md`) before touching pc3's
  index or running lake in pc3; then rebase `codex/pc-entry23` onto pc3's HEAD and do steps 3-7.

## Step 2: closure estimate (computed on pc3's working tree at 88a4eec5a + untracked lane files)
- Their diff 286e17a8c..514704634: 100 files = 29 added modules, 70 modified modules, root aggregate.
- Only path collision with pc3's untracked files: `Surgery/Topology/HistoryBallVolume.lean` (CP1's copy;
  ACC11 is committing it -> removal commit in pc23 before the cherry-picks, so the original wins).
- Reverse-import closure of the 70 modified modules (script `cp2/rclosure.py`): 4136 modules = 4100 tracked
  + 36 untracked lane files (these lanes' read-only compiles will see rebuilt upstream oleans).
- Deepest seeds (longest downstream import chain): `Geometry/Metric/Convergence/Metric/Evaluation` (170;
  +52 lines, e2c840b33), `Geometry/Connection/ParallelTransport/Frame` (153; +177/-1, ac2e5266e),
  `Analysis/Calculus/Manifold/AbsolutelyContinuous` (135; 5f4118086, 9c21472a6),
  `Geometry/Curvature/Naturality/Pullback/LocalCross` (133; e582442c6), `Bishop/CompactBall` (125; c569a9285).
  All foundational edits are pure appends (checked for the five above), so breakage downstream is unlikely
  but the rebuild is ~4100 of ~7600 modules (effectively a large fraction of a full-tree build).

## Step 1: cherry-picks in pc23 (`git cherry-pick -x`, rerere on via `-c`, in order)
Resolution rule: keep OUR statements (I28, 06a347488/950618ee3: explicit `Ctime`/`hbound` derivative
hypothesis instead of `hC2` + `W.time_derivative`), take THEIR new declarations and proof routes, feeding our
`hbound` where they derived it from `W.time_derivative`. Statement identity of our public theorems checked
with `cp2/stmt.py` (text of the statement up to `:= by`, HEAD vs resolved).

1. ca4585835 -> 20bd7ba59, 3 conflicts:
   - `Surgery/Topology/DiscardedCanonicalCoverage.lean` (body of
     `exists_late_canonical_on_discarded_core_with_cap_neck_charts_of_canonical_neighborhoods`): their new
     private `exists_late_scalar_gt_on_discarded_core_of_pinching` + public `exists_late_scalar_gt_on_discarded_core`
     kept; body = their call to the private helper with OUR `hbound` (their local `have hbound … W.time_derivative`
     dropped). Both public statements unchanged vs ours.
   - `Surgery/Topology/TerminalComponentClassification.lean` (body of
     `exists_component_poincareStandard_tolerance_of_canonical_neighborhoods`): their new
     `…_of_spatial_neighborhoods` kept; our theorem (statement unchanged) now proved through it:
     `hclass … q q R Ctime hq hqR hbound c ?_ hterminal` + their spatial branch verbatim.
   - `Surgery/Topology/DiscardedComponentClassification.lean`: took THEIR file (private boundary lemma in
     their spatial form, new `exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods`), then
     restored OUR statement of `exists_poincareStandardDiscarded_tolerance_of_canonical_neighborhoods`
     (extra `∀ Ctime, hbound →`): their proof with `Ctime`/`hbound` passed to the spatial theorem in place of
     `⟨C2,_⟩`/`W.time_derivative`; OUR body of `exists_poincareStandardDiscarded_cutting_scale_of_incoming`
     (passes `⟨C, _⟩` and `.choose.time_derivative`). All three public statements identical to ours.
2. 53943deb3 -> 6c8b3ccc3, 0675a35e5 -> 2ffedc4ac, 9c21472a6 -> 627ae688b, 4adbb5f4d -> a096e35d0: clean.
3. 5c0f13a99 -> 68b77a071, 1 conflict: `Surgery/Contract/PoincareHornCutoffRecord.lean` ~:433, both sides
   add a declaration after `canonical_neighborhoods_of_incoming_heq` (ours: private
   `derivative_bound_of_incoming_heq`; theirs: `MetricCutCapEvent.exists_poincareStandardDiscarded_tolerance_of_spatial_neighborhoods`).
   Union, ours first.
4. c14fd1691 .. 514704634 (32 commits): no source conflicts; the root aggregate conflicted in 11 of them
   (d1c4672a1, 89e6d5ae0, b3604787e, 5c9585721, 1ea780dd4, 413638577, cbe733665, f36eb0d44, 2c5992f1d,
   ac2e5266e, bb215824d; each: our side + that commit's added import lines inserted after the last
   alphabetically smaller sibling in the same folder, script `cp2/agg.py`). All 29 added modules registered
   once; no import line removed. CP1-relocated commits ebefde69b, c569a9285, 514704634 applied in place
   (their form; HistoryBallVolume added by c569a9285 since pc23's base has no CP1 copy).
   700ae358a: strengthens the conclusion of
   `RetainedCoreHistory.exists_compatible_historical_solution_limits_at_scalar_escape_of_scalar_derivative_contact`;
   no consumer anywhere in our tree (committed or untracked), so no repair.
   Result: 41 cherry-picks 20bd7ba59..0725989eb on top of 88a4eec5a; the 95 files touched only by them are
   byte-identical to 514704634; differences vs their tip only in the aggregate and the 4 both-sides files.
5. Source scan of their 99 Lean files: no sorry/admit/axiom/nolint/heartbeat/diagnostics/comments added; one
   pre-existing `set_option backward.isDefEq.respectTransparency false in` (TerminalSphericalBarrier:193,
   present at the merge-base; 529 files use it).
6. Name clashes (script `cp2/names.py`, 234 new public names vs our files since the merge-base + pc3's
   untracked files): besides the 5 CP1 copies (deleted at step 3), FIVE exact full-name clashes between c14fd1691
   (`TerminalNeckNormalization`, `TerminalSphericalBarrier`) and our committed
   `Surgery/Topology/TerminalSpatialCanonicalAlternatives` (950618ee3), which IMPORTS both -> hard error.
   Our follow-up commit 49c168b8a (ours, not theirs):
   - `SpatialNeck.exists_terminal_neckBuffer_pullback_bound`, `TerminalLimitMetric.eventually_normalizedNeck_of_moving_spatialNecks`:
     identical statements -> our copies (+ their two private helpers) deleted, upstream used.
   - `TerminalLimitMetric.eventually_normalizedNeck_of_spatialNecks`: ours has no capture/regularity
     hypotheses, consumed only inside its file -> OURS renamed `…eventually_normalizedNeck_of_incoming_spatialNecks`.
   - `TerminalLimitMetric.eventually_spatialNeck_of_incoming_spatialNecks`,
     `…exists_neck_spherical_barrier_of_incoming_spatialNecks`: theirs carry an extra scalar
     time-derivative hypothesis; ours is consumed by `Contract/TerminalCorePresentationOfSpatiallyCanonical:103`
     -> THEIRS renamed `…_of_scalar_derivative_bound` (only consumer: each other, in TerminalSphericalBarrier).
7. ACC11 pushed e68bf6466 (CP1 files NOT committed, still untracked in pc3). pc23 rebased onto e68bf6466
   (rerere), no conflicts; 42 commits. Waiting for ACC12's push (full-tree build running) before step 3.
- Build plan: 4100 closure modules cannot be passed on the Windows command line (~330k chars); since every
  committed module is in the root aggregate and ACC12's full build leaves all others fresh (hash-based),
  target `DifferentialGeometry` (+ `…Skeleton.PoincareEndgame`) rebuilds exactly the closure; untracked lane
  files are not built.

## REDIRECT (lead, owner decision): relocation mode
- ff-merge and closure build ABANDONED; no lake / no index use in pc3. `codex/pc-entry23` (42 commits:
  41 cherry-picks + 49c168b8a) pushed once to `liao` as a record (new branch) and left there.
- Relocation of the ILB-relevant code into pc3 as NEW untracked files only; source = pc23 tree
  (= e68bf6466 + the cherry-picks). Scripts in `cp2/`: `delta.py` (per-module declaration delta, ours
  e68bf6466 vs pc23), `need.py` (reference fixpoint), `gen.py`+`chunker.py` (sibling bodies with exact scopes),
  `assemble.py` (imports, `open private`), `materialize.py`, `cc.sh` (read-only compile).
- Delta of the 53 modified modules in the import closure: all additive except body-only changes
  (ParametricIntervalContinuity, InitialMetricTimeBounds, FamilyContinuity x2, AdaptedField/Existence,
  Geodesic/Family x2, SmoothExtension, Hamilton/Ancient, CurveEndpointPerturbation: proofs only, ours kept),
  one statement change (`continuousOn_lVelocity_family`, FamilyContinuity) and two removals
  (`exists_parFrame`, AdaptedField/Existence; `regularizedStage_endpoint_clocks`, private in our Density,
  public in their HistoryAction). Six files changed only `open scoped … Topology` -> `_root_.Topology`.
- Reference fixpoint (names used by the relocated text): 10 added modules minus PhaseFamily (unreferenced)
  = 9 verbatim copies + 25 sibling files; `continuousOn_lVelocity_family` is NOT referenced, so no renamed
  copy was needed (rule 3 did not trigger). Not relocated ("available in codex/pc-entry23"): the 19 other
  modified modules' additions (UpperSupport/Monotonicity, Pointed/Convergence/Distance,
  ParallelTransport/Frame, Pullback/LocalCross, InitialMetricTimeBounds, Regularized/FamilyContinuity,
  AdaptedField/{Existence,InnerProduct}, Geodesic/{Congruence,SmoothExtension}, Hamilton/Basic,
  HistoryAction/MinimumTime, HistoryCapPreservation, HistoryPoleAction, Metric/Evaluation,
  Metric/InverseComposition, Distance/LocalPullCompactness, ChartCurvature/Scalar, CurveEndpointPerturbation),
  the added modules outside the closure (VariationPairing, Curve/{EndpointDerivative,VelocityFamily},
  TerminalTimeConvergence, Regularized/Finite{First,Second}Variation, AdaptedField/{FiniteChain,LocalPullback},
  Geodesic/{FamilyContinuation,FamilyLift,LocalPullback,PhaseFamily}, Hamilton/FiniteChain, Index/FiniteChain,
  EventFirstVariation, HistoryAction/GeodesicFamily, SlabScalarDerivatives, SurvivorGeodesicFamily,
  SurvivorIndexBoundary, LocalDiffeomorph/FamilyLift) and everything of the discarded/terminal-classification
  commits (ca4585835, 5c0f13a99, c14fd1691, 700ae358a).
- Sibling rules applied: imports = original module + imports their version added to it + relocated modules
  whose names the body uses; exact scopes (`set_option`, `noncomputable section`, `open`, `namespace`,
  `variable`, `omit … in`, `attribute … in`, `private local instance`, `local notation`) copied from their file,
  declarations present in ours dropped (with their `… in` prefixes), empty namespace blocks pruned; private
  declarations of OUR original used by the additions reached with `open private … from <original>` inside the
  matching namespace (StandardScalarComparison `E3`; InitialWindowBounds; TerminalAction ×2).
- Compile (`cc.sh`: lean.exe directly, no lake, `LEAN_PATH` = scratch oleans + shared build + packages,
  lakefile options, `LEAN_NUM_THREADS=2`, modules renamed `CP2S.<name>`; scratch root reached through
  `subst P:` because the full paths exceed MAX_PATH). 29 of 34 compile with no output. 5 blocked by
  COMMITTED modules without an olean in the shared build (`StandardCap/WindowDiscarding`,
  `Topology/HistoryActionJoin`): FirstCapDiscarding, WindowEvolution, HistoryAction/TimeContinuity,
  HistoryAction/EventContinuation, CapWindowActionRegularCrossing — retry once ACC12's full build produced them.

## Relocation result (files now in pc3, untracked; LF endings)
Provenance for the commit message: relocated as new files from origin/codex/pc-sorry-free 53943deb3 0675a35e5 9c21472a6 ebefde69b a12152e86 baadd3cae 5f4118086 d1c4672a1 89e6d5ae0 b3604787e ac24dded4 1ea780dd4 2425dbcaa 413638577 f36eb0d44 31059bcb8 01b8f23b0 095307685 4538bed95 c569a9285 514704634 (the 21 commits touching the source files); authors Bennett Chow, Ziyang Qin. (Exact per-file source: the pc23 tree = e68bf6466 + cherry-picks, branch codex/pc-entry23 on liao.)

| File (under DifferentialGeometry/) | Kind | Original | Lines | Compile |
|---|---|---|---|---|
| `Analysis/Calculus/Manifold/AbsolutelyContinuousPartition` | sibling (additions) | `Analysis.Calculus.Manifold.AbsolutelyContinuous` | 154 | clean (0 msgs) |
| `Analysis/Parabolic/TimeSobolev/Curve/ManifoldAbsolutelyContinuous` | added, verbatim | `-` | 51 | clean (0 msgs) |
| `Geometry/Comparison/Volume/Bishop/CompactBallRatio` | sibling (additions) | `Geometry.Comparison.Volume.Bishop.CompactBall` | 113 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Perelman/LGeometry/Action/Estimates/PrefixBound` | sibling (additions) | `Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Boundary` | 34 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Perelman/LGeometry/Action/LocalPullbackLagrangian` | sibling (additions) | `Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback` | 61 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Perelman/LGeometry/Action/Minimizer/CarrierC1RegularityAbsolutelyContinuous` | sibling (additions) | `Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity` | 78 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Perelman/LGeometry/Action/Minimizer/C1RegularityAbsolutelyContinuous` | sibling (additions) | `Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.C1Regularity` | 49 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Perelman/LGeometry/Action/Minimizer/PrefixMinimalityAbsolutelyContinuous` | sibling (additions) | `Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimality` | 106 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Perelman/LGeometry/Action/Minimizer/EulerLagrangeRegularityAbsolutelyContinuous` | sibling (additions) | `Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.EulerLagrangeRegularity` | 185 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Perelman/StandardSolution/StandardScalarLowerBound` | sibling (additions) | `Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarComparison` | 34 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/StandardCap/FirstCapDiscarding` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowDiscarding` | 138 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/StandardCap/InitialWindowScalarLowerBound` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds` | 112 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistorySurvivorIncomingPrefix` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingTerminal` | 64 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/StandardCap/PreparedCapCommonFlow` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowCommonFlow` | 178 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/StandardCap/WindowEvolution` | added, verbatim | `-` | 240 | clean (0 msgs) |
| `Topology/Manifold/LocalDiffeomorph/IntervalLiftAbsolutelyContinuous` | sibling (additions) | `Topology.Manifold.LocalDiffeomorph.IntervalLift` | 116 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/EventActionCompetitor` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.EventAction` | 294 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryActionBackwardClock` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction` | 155 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/TerminalActionCompactness` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.TerminalAction` | 1551 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/AbsoluteContinuityMinimizer` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.AbsoluteContinuity` | 1833 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/Attainment` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density` | 167 | clean (0 msgs) |
| `Topology/Order/Semicontinuity` | added, verbatim | `-` | 64 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/TimeContinuity` | added, verbatim | `-` | 814 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/EventContinuation` | added, verbatim | `-` | 256 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryParabolicBallCrossing` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.HistoryParabolicBall` | 60 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/MetricCutCapRegularCrossing` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower` | 41 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/CapWindowActionRegularCrossing` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowAction` | 1522 | clean (0 msgs) |
| `Geometry/Measure/ParametricIsometry` | added, verbatim | `-` | 39 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/SurvivorChartMetricInner` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric` | 50 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/EventParametricDensity` | added, verbatim | `-` | 32 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryAction/EndpointContinuity` | added, verbatim | `-` | 116 | clean (0 msgs) |
| `Geometry/Metric/Distance/CompactMinimizerInwardPoint` | sibling (additions) | `Geometry.Metric.Distance.CompactMinimizer` | 70 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryBallVolume` | added, verbatim | `-` | 2040 | clean (0 msgs) |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryReducedDensityMeasurable` | sibling (additions) | `Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedDensity` | 88 | clean (0 msgs) |

- All 34 compile read-only with no output (lean.exe direct, no lake, 2 threads, lakefile options), final clean
  sequential run in dependency order (`cp2/order.txt`, log `cp2/cc.log`).
- Committed modules without an olean in the shared build, scratch-built under the renamed root
  `CP2C.<name>` into `cp2/out` (source = pc3 HEAD, nothing written under E:): `Surgery/StandardCap/WindowDiscarding`,
  `Surgery/Topology/CapWindowAction`, `Surgery/Topology/HistoryActionJoin` — the acceptance lane must build them for real.
- Verbatim added modules: no textual change (HistoryBallVolume now keeps its original imports
  `CompactMinimizer`/`CompactBall` and additionally imports the three sibling files; CP1's copies replaced).
- Siblings: duplicate scope lines of their appended self-contained blocks (repeated `set_option autoImplicit
  false`, `noncomputable section`, identical `open`s in the same scope) removed; nothing else edited.
- Source scan: no sorry/admit/axiom/nolint/heartbeat or diagnostic options, no comments/docstrings;
  `set_option autoImplicit false` only.
- Name clashes (`cp2/clash.py`, 110 public declarations vs every other .lean file on disk in pc3, committed and
  untracked): NONE (full or short name). The TerminalSpatialNeck clash of pc23 does not arise (those modules
  are not relocated). Module paths: only the 5 CP1 paths existed (untracked, overwritten).
- Audit (`cp2/src/AuditCp2R.lean`, scratch, lean.exe direct, `maxHeartbeats 0` in the scratch file only):
  175 declarations (168 theorems) of the 34 modules; axioms all within {propext, Classical.choice, Quot.sound},
  no `sorryAx`; the 13 standard linters (docBlame excluded): 0 findings. 21 G0 headlines printed with
  `[propext, Classical.choice, Quot.sound]` (log `cp2/log/audit2.log`).
- ANALYSIS_ILB.md: appended "Post-relocation gap map". FILL_QUEUE.md NOT edited (tracked ledger; ACC12 is
  using the index) — lead to set entry 23 = relocated/awaiting acceptance, 24a/24b unblocked for G0.
- Scratch: `subst P:` maps to `cp2/` (remove with `subst P: /d` when done); worktree D:\differential-geometry-pc23
  kept as read source (branch codex/pc-entry23 pushed to liao).
- DONE.
