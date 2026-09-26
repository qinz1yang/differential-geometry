# Lane CP1: collaborator's uniform ball-volume bounds as new files (2026-09-26)

Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf`, HEAD 1640a9e11. No git writes,
no `lake build`, no edit to any committed file, `DifferentialGeometry.lean` untouched.

## Provenance (for the acceptance commit message)

Cherry-picked as new files from `origin/codex/pc-sorry-free` ebefde69b, c569a9285, 514704634;
authors Bennett Chow, Ziyang Qin.

| New file (paths under `DifferentialGeometry/`) | Lines | Source commit | Original path | Author / committer |
|---|---|---|---|---|
| `Geometry/Comparison/Volume/Bishop/CompactBallRatio.lean` | 94 | c569a9285 | `Geometry/Comparison/Volume/Bishop/CompactBall.lean` (+65, appended) | Bennett Chow / Ziyang Qin |
| `Geometry/Metric/Distance/CompactMinimizerInwardPoint.lean` | 69 | c569a9285 | `Geometry/Metric/Distance/CompactMinimizer.lean` (+49, appended) | Bennett Chow / Ziyang Qin |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryParabolicBallCrossing.lean` | 59 | ebefde69b | `…/Surgery/Topology/HistoryParabolicBall.lean` (+56, appended) | Bennett Chow / Ziyang Qin |
| `Geometry/Flow/RicciFlow/Surgery/Topology/MetricCutCapRegularCrossing.lean` | 42 | ebefde69b | `…/Surgery/Topology/MetricCutCapScalarLower.lean` (+39, appended) | Bennett Chow / Ziyang Qin |
| `Geometry/Flow/RicciFlow/Surgery/Topology/HistoryBallVolume.lean` | 2038 | c569a9285 + 514704634 | same path (new in c569a9285, +101 in 514704634) | Bennett Chow / Ziyang Qin (c569a9285); Ziyang Qin (514704634) |

The four originals in our tree are byte-identical to their parents in the source commits
(`git diff ebefde69b~1 HEAD` / `c569a9285~1 HEAD` shows only the appended blocks), so the appended
declarations elaborate against the same base.

Declarations:
- `CompactBallRatio`: `VolumeComparison.volume_mul_pow_le_of_local_ricci_lower_bound`.
- `CompactMinimizerInwardPoint`: `Riemannian.exists_inward_point_and_minimizer_of_isCompact_closedBall`.
- `HistoryParabolicBallCrossing`: `ObservedHistory.isParabolicallyRmControlledBall.exists_regularCrossing_at_event_time`,
  `….regularCrossing_of_oldOutput_at_event_time`.
- `MetricCutCapRegularCrossing`: `MetricCutCapEvent.exists_regularCrossing_or_cap`,
  `MetricCutCapEvent.regularCrossing_or_cap_of_admissible_node`.
- `HistoryBallVolume`: public `ObservedHistory.csSup_parabolicallyRmControlledBall_eq_or_cap_or_curvature_eq` (709),
  `ObservedHistory.ball_subset_backwardSurvivorDomain_and_closed_trace_isRmControlled` (904),
  `ObservedHistory.exists_inward_point_with_earlier_volume_comparison` (1531), headlines
  `ObservedHistory.exists_uniform_terminal_ball_volume_lower_of_cap_contact` (1773) and
  `ObservedHistory.exists_uniform_terminal_ball_volume_lower_of_initial_time_contact` (2008); the rest private.
  All public names are unique library-wide (grep).

## Textual changes (everything else verbatim)

1. `CompactBallRatio`: new imports `Geometry.Metric.Distance.Ball` and `Geometry.Comparison.Volume.Segment.Count`
   (the two imports c569a9285 added to `CompactBall.lean`) plus `…Bishop.CompactBall`; reconstructed the
   enclosing scope of `CompactBall.lean` exactly: `set_option autoImplicit false`, `noncomputable section`, the
   file's `open`/`open scoped` lines, namespace `DifferentialGeometry.Geometry.Riemannian.VolumeComparison`
   and its six `open`s, the three `variable` blocks, `attribute [local instance]
   Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace`. Omitted the
   original file's three `private local instance`s, the `F₀` notation and the private `MeasurableSpace E`
   instances: the theorem (declared with `attribute [-instance] … in`) uses none of them; it compiles
   without them. Two trailing blank lines before `end` reduced to one.
2. `CompactMinimizerInwardPoint`: import `…Distance.CompactMinimizer`; reconstructed the second section of
   `CompactMinimizer.lean` (lines 312–328 there): `set_option autoImplicit false`, `noncomputable section`,
   opens, namespace `DifferentialGeometry.Geometry.Riemannian`, `open Exponential`, `open HopfRinow`, the
   `variable` block. Trailing double blank line reduced to one.
3. `HistoryParabolicBallCrossing`, `MetricCutCapRegularCrossing`: one import of the original module plus
   `set_option autoImplicit false` (the original files set it at their top); the appended blocks are
   self-contained sections (own `noncomputable section`, `open`, `namespace`, `universe`, `variable`) and
   are copied verbatim.
4. `HistoryBallVolume` (text at 514704634): imports repointed — `…Distance.CompactMinimizer` →
   `…Distance.CompactMinimizerInwardPoint`, `…Bishop.CompactBall` → `…Bishop.CompactBallRatio`, and
   `…Topology.MetricCutCapRegularCrossing` added (it uses `exists_regularCrossing_or_cap` at line 612). It
   does not use the `HistoryParabolicBallCrossing` lemmas, so that file is not imported by it (register it
   in the root aggregate separately).
5. Comments/docstrings: none in any source block (checked, `--` and `/-` absent); none stripped. No copyright
   header in the sources, matching the tree's convention (`linter.style.header = false`).
6. No interface repair was needed: every block compiles unchanged against our branch (06a347488's revision
   of `PresentedStaticCap`, records, `BackwardPointTrace` does not touch what they use).

## Compile (read-only, `LEAN_NUM_THREADS=2`, project options incl. `weak.linter.mathlibStandardSet`)

- `CompactBallRatio` 0 errors, 0 warnings (23 s); `CompactMinimizerInwardPoint` clean (21 s);
  `MetricCutCapRegularCrossing` clean (28 s); `HistoryParabolicBallCrossing` clean under the lakefile options
  (the only message without `linter.style.longLine=false` is a long `open` line copied verbatim; the
  lakefile disables that linter).
- `HistoryBallVolume`: 0 errors, 0 warnings (70 s), compiled as a renamed scratch module against scratch
  oleans of the three new siblings. The shared build has NO olean for the committed module
  `Geometry/Comparison/Volume/CompactSmallBall` (imported by `HistoryBallVolume`; 38 lines, deps built);
  I compiled it as a scratch module as well. The acceptance build must build it (it is in the root).
- Scratch under `…\scratchpad\cp1\` only; axiom probes deleted.

## Axioms

`propext, Classical.choice, Quot.sound` (no `sorryAx`) for both headlines,
`volume_mul_pow_le_of_local_ricci_lower_bound`, `exists_inward_point_and_minimizer_of_isCompact_closedBall`,
`regularCrossing_or_cap_of_admissible_node`, and both `HistoryParabolicBallCrossing` lemmas.

## Overlap note

`Bishop/LocalBallRatio.lean` (lane SS1, untracked) `riemannianBallOf_volume_ratio_ge_of_ricci_lower` needs
`RiemannianMetricComplete g`; `volume_mul_pow_le_of_local_ricci_lower_bound` needs only a compact closed
`R`-ball. Same Bishop–Gromov content, different normal form; the complete version could become a
corollary later (entry "merges").

## Consumer check: 24a / 24b and the initial-lower-bound leaf

Leaf: `historyReducedVolumeInitialLowerBound` (`Surgery/Skeleton/PoincareEndgame.lean:30`), statement
`HistoryReducedVolumeInitialLowerBound` (`Surgery/Topology/NoncollapsingThroughSurgeryLeaves.lean:113`),
conclusion `ReducedVolumeBoundedBelowBefore c r₀ ε t₀` (`:61`): `ofReal c ≤ H.reducedVolume … t (√t)`.

**Verdict: neither headline supplies 24a or 24b.** Both conclude a *Riemannian ball volume* bound
`ofReal κ * ofReal r ^ 3 ≤ vol B_t(p, r)`, not a bound on `reducedVolume`/`regularizedCost`.
- 24a (`exists_uniform_regularMinimizerEndpoint_of_regularizedCost_lt`, `ANALYSIS_ILB.md:60–78`): the
  cap-point action barrier for L-curves. Nothing in the five files deals with L-length, `regularizedCost` or
  `regularMinimizerEndpoints`. It stays fully open (G0–G3 of `ANALYSIS_ILB.md:81–85`, still blocked on entry 23).
- 24b (`exists_uniform_initial_regular_block`, `ANALYSIS_ILB.md:90–111`, plus `reducedVolume_ge_of_initial_block`):
  its only volume ingredient, `vol_{g₀} B(q₀, ρ) ≥ κ₀ ρ³`, is what the initial-time headline also uses
  (`Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound` plus the
  `InitialIdentification` local-isometry transfer, `HistoryBallVolume.lean:2020–2034`), and that was already
  available on our branch (`ANALYSIS_ILB.md:134–135`). L1 (`l_min ≤ 3/2` through surgeries, 700–1100 lines),
  L2 (endpoint perturbation, 300–450) and L3 (block assembly, 200–300) remain missing as listed at
  `ANALYSIS_ILB.md:118–135`.

**What the headlines do supply:** the two boundary branches of the maximal-radius trichotomy
`csSup_parabolicallyRmControlledBall_eq_or_cap_or_curvature_eq` (`HistoryBallVolume.lean:709`) for a
*direct* proof of `NoncollapsedAboveBefore` (`NoncollapsingThroughSurgeryLeaves.lean:53`), i.e. of the
conclusion that the reduced-volume chain produces through `noncollapsedAboveBefore_of_reducedVolume_bounds`
(`:191`):
- the maximal controlled radius `σ` stops because a backward trace of a point of `B̄_t(p,σ)` lands in a
  surgery cap at an event time in `[t − σ², t]` → `…_of_cap_contact` (`HistoryBallVolume.lean:1773`).
  The cap `S` and `S.hasCanonicalWindow` come from the class: `GeometricCutoffRecord.static`
  (`Surgery/Topology/GeometricCutoff.lean:244`, parameters `(fixed, modelRadius, modelOrder,
  modelAccuracy)`) and `hasCanonicalCutoffRecords` (`Surgery/Topology/CanonicalCapWindows.lean:103`);
  the side conditions `ε ≤ ε₀`, `2 ≤ m`, `4·transitionEnd + 6 ≤ D` fit the leaf's `εcap`, `mcap`, `Dcap`.
  The trichotomy's `hOld` (old = retained core) is to be read off `RetainedCoreHistory`.
- `σ = √t` (the parabolic ball reaches time 0) → `…_of_initial_time_contact` (`HistoryBallVolume.lean:2008`),
  only for `σ ≤ ρ(g₀)`.
- NOT covered: the third branch (the radius is limited by curvature `σ⁴|Rm|² = 1` at a traced point, with
  traces surviving to a time before `t − σ²`), and the initial-time branch with `√t > ρ(g₀)`.

**What is still missing to prove the leaf as stated:** all of 24a and 24b (unchanged, above). Using the new
headlines would need an interface change of the assembly
`noncollapsingThroughSurgery_of_reducedVolume_of_smallScale` (`NoncollapsingThroughSurgeryLeaves.lean:242`)
so that the reduced-volume lower bound is demanded only in the curvature-limited branch, combined with
`volume_mul_cube_le_of_smaller_controlled_radii` (private, `HistoryBallVolume.lean:1679`) or the public
headlines for `r ≤ σ`. That does not shrink 24a/24b: the barrier concerns L-curves anywhere in the history,
not only near the ball, and the initial block is about time-0 endpoints. (A controlled `r`-ball never
touches a cap anyway: its points have traces back to `t − r²`; cap contact only occurs at the maximal radius
`σ`.) So the headlines give a reduced-volume-free route to `NoncollapsedAboveBefore` in the two boundary
branches only; they do not prove any part of the reduced-volume leaf.
