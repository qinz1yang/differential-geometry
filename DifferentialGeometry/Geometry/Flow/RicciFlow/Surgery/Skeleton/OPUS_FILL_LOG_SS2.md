# OPUS_FILL_LOG_SS2 — small-scale bricks S0 (+ S0-def) and S6

Design: `Skeleton/DESIGN_SMALLSCALE.md` §3 (S0-def, S0, S6), §6.5 rows 8–9. Worktree
`D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf`. New files only; no builds, no git
writes; compiles by `lake env lean` (2 threads, lakefile options).

## 2026-09-26

- Probe (scratchpad `ss2/Probe.lean`): S0-def, S0 and S6 elaborate verbatim with `sorry` bodies
  (0 errors). `H.time i = H.toHistory.time i` is `rfl`.
- S6 route change (simpler than the design, same statement):
  - No curvature control is used. The initial-slab volume estimate
    `RicciFlow.exists_uniform_initial_ball_volume_lower_bound` (`Estimates/InitialVolume.lean`)
    bounds every small ball for `t ≤ τ(g₀)`, whatever the curvature. New general corollary
    `exists_uniform_initial_closedSlab_ball_volume_lower_bound` (a `ClosedSlab 0 b` twin of
    `exists_uniform_initial_ball_volume_lower_bound_of_isometry`, which only covers `IncomingSlab`,
    i.e. excludes the right endpoint; the history slice at `t` is `closedPrefixAt t`).
  - No event before `η` does **not** need `ρbound`: every `GeometricCutoffRecord` carries
    `singular : (event i).incoming.SingularEndpoint`, and
    `exists_pos_le_singular_incoming_time_of_initialIdentification` (`InitialCurvatureLifespan.lean`)
    then gives `a₁(g₀) ≤ time 1`. So `η := min τ (a₁/2)` forces `activeStage t = 0`. The design's
    `ρbound ≤ ρ₁` premise is kept verbatim (`ρ₁ := 1`) but unused; the "record neck scale vs.
    terminal curvature" sub-brick of §1.6 is not needed.
  - Radii above the estimate's `ρ` are handled by `r ≤ 1` and monotonicity: `κ := κ_v·min(ρ,1)³`.
- S0 route: as designed, with explicit constants.
  - New reusable lemma `ObservedHistory.exists_isParabolicallyRmControlledBall_earlier_volume_le`:
    a controlled ball `(t,p,r)` and any `t' ∈ (t − r²/9, t)` give `p'` with a controlled ball
    `(t', p', r/8)` and `vol_{t'} B(p', r/8) ≤ e³ · vol_t B(p, r)`.
  - Proof: common flow `S` on `U = B_t(p,r)` (`HistoryParabolicBall.lean:860`); metric distortion
    `S(t) ≤ e²S(t')`, `S(t') ≤ e²S(t)` on all of `U` (`inner_le_exp_mul_inner_of_rmNormSq_le`, curvature
    radius `r`, `t − t' ≤ r²/9`); frontier of `K` at `S(t')`-distance `≥ r/6`
    (`riemannianBallOf_subset_of_inner_le_mul`, `e < 3`), hence the closed `S(t')`-ball of radius `r/6`
    lies in `K` (`riemannianEDistOf_closedBall_subset_of_le_frontier_distance`) and is compact; image of the
    `r/8`-ball under `f_{t'}` is the stage ball (`image_riemannianBallOf_localPullMetric`); traces are
    `f_k w`; volume through `riemannianVolumeMeasure_image_eq_of_injective_local_isometry` and
    `riemannianVolumeMeasure_apply_le_of_inner_le`, then `U ⊆ B_t(p,r)`.
  - The ForwardTransfer volume lemma (`:126`) was not used: it ties the curvature radius to the ball
    radius, which would put `e^{9·64}` into the constant; the pointwise lemma (`:91`) with curvature
    radius `r` is used instead.
  - `c := 1/(512·e³)`: `κ(r/8)³ ≤ vol_{t'} ≤ e³ vol_t`. A regular `t'` exists because the event
    times are finite (`Ioo_infinite.sdiff (finite_range time)`).
- Files:
  - `Surgery/Topology/HistoryNoncollapsingSliceTransfer.lean` (S0-def, S0, transfer lemma).
  - `Surgery/Topology/InitialLayerNoncollapsing.lean` (S6 + closed-slab volume corollary).
- Compile blocked for a while: the acceptance lane's cascade was rewriting oleans
  (`Estimates/InitialVolume`, `CompactSmallBall`, `BackwardFlowReducedLength` missing mid-build).

## 2026-09-26 (resumed lane)

- Resume: both files on disk and complete, no `sorry`. Statements of S0-def, S0 and S6 match §3
  verbatim (S6 keeps the unused `ρbound ≤ ρ₁` premise as designed, `ρ₁ := 1`).
- Shared build lacks the oleans of three committed prerequisites (`Comparison.Volume.CompactSmallBall`,
  `Estimates.InitialVolume`, `Surgery.Topology.InitialVolume`; no lake running). Emitted them to
  scratch `ss2b/olean` (root `SS2B`, `ss2b/scomp.sh`), no edits.
- Compile (2 threads, lakefile options, `weak.linter.mathlibStandardSet=true`): both files 0 errors,
  0 warnings.
  - `HistoryNoncollapsingSliceTransfer.lean`: 273 lines.
  - `InitialLayerNoncollapsing.lean`: 152 lines.
- `#lint` (all 14 env linters) in probes: only `docBlame` on the S0-def (inapplicable per AGENTS.md);
  S6 file passes all.
- Axioms (`#print axioms`, probes removed): `exists_noncollapsedBefore_of_regularTimes`,
  `ObservedHistory.exists_isParabolicallyRmControlledBall_earlier_volume_le`,
  `exists_initial_layer_noncollapsed`, `exists_uniform_initial_closedSlab_ball_volume_lower_bound`:
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Public names unique library-wide; SS3's file imports both modules and holds its own private copy of
  `ball_volume_lower_bound_of_closedSlab_stage_zero` (private, no clash).
- Deviations from §3: none in statements. Routes differ (recorded above): S6 uses the initial-slab
  volume estimate and first-singular-time lifespan instead of curvature control; S0 uses the pointwise
  distortion lemma (`ForwardTransfer:91`), constant `c = 1/(512·e³)`.
- Lane SS2 closed.
