# OPUS fill log X: bricks X1–X3 (horizon extension), DESIGN_C2_ASSEMBLY §5.4

Worker lane X, 2026-09-26. Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf`.
Route fixed by `Surgery/consult/H5-horizon-extension-review-digest.md`. New file only:
`Surgery/Topology/HistoryHorizonExtension.lean`. No existing file modified.

## Log

- Probe P1 (all §5.4 X statements with `sorry` bodies, verbatim): elaborated, 0 errors.
- Easy transfer lemmas: `Fin.lastCases_last/_castSucc` do not fire by `rw`/`simp` on
  `(H.extendHorizon …).toHistory.*` at index `Fin.last H.eventCount` (the `Fin.last` argument is
  `H.eventCount`, the history's is `(H.extendHorizon …).eventCount`); `erw` after `unfold` works.
  `activeStage` of the extended history at `⟨t.1, _, _⟩` is `rfl`.
- X1 non-degenerate case: G1 on `H.finalSlab hlt` with `S.smoothUpTo.jointContMDiffOn`, then pick
  `T' ∈ (horizon, d)` and restrict (`timeRestrict` + `MetricSmoothUpTo.of_contMDiffOn_Ico`), since a
  closed slab on the full `[a, d]` needs an open-neighbourhood joint smoothness G1 does not give.
  Degenerate case: G0 `exists_closedSlab_of_metric` from `initialMetric last` at `time last`.
- X2: same-curve comparison. `regularizedStageStart` agrees for `T ≤ horizon` (any `u`: `T - u² ≤ T`),
  `regularizedStageEnd` is definitionally equal; the Lagrangians agree a.e. on the segment window
  `Ioo start end` because `T - t²` lies in the OLD stage domain there (`mapsTo_regularizedStage_Ioo`)
  and `stageMetric_extendHorizon`; hence equal extended actions, equal action-value sets (the
  `T - u² ∈ Icc (time last) (stageEndTime last)` and `T - v² ∈ stageDomain first` side conditions are
  equivalent because `T - u², T - v² ≤ T ≤ horizon`), equal cost, density and minimal-endpoint set.
  The `first` index agrees (`projIcc` values agree as reals). Endpoint measure: if
  `T - v² ∈ stageDomain first` the endpoint metrics agree; otherwise the density is `0` on both sides
  (empty action-value set), so both integrals vanish. No `historyLExp` comparison, no claim that the
  endpoint measures coincide in general. `rw` through `reducedVolume`'s dependent `dite` fails (its
  `IsManifold` instance proofs are abstracted to `reducedVolume._proof_*` specialised to the original
  `first`); fixed with two private unfolding lemmas proved by `subst; exact dif_pos/dif_neg`.
- X3: the `BackwardPointTrace` of the old history is re-packaged field-for-field for the extended
  history (the structure types are not defeq because the `ObservedHistory` argument differs), and
  the curvature clause transfers through `stageMetric_extendHorizon` at `activeStage_mem`.
- Final compile: the shared `.lake` lost a few oleans in the killed 1212-module cascade
  (`Riemannian/MetricComparison`, `Parabolic/Dirichlet/Energy`, `WithBoundary/DirichletWeakFormChart`,
  `Family/CompactSupportContinuity`). Per the lead's scratch-module pattern: hard-linked the existing
  build oleans into a scratch tree on E: (outside the build dir), compiled the 4 missing HEAD modules
  into it, `LEAN_PATH = scratch;lake env path`, `LEAN_NUM_THREADS=2`. Scratch tree deleted afterwards.
  In the final file `congr 1` at the `limsup` hit a `whnf` heartbeat timeout; replaced by an explicit
  `congrArg (fun f => limsup f atTop)`; the density rewrite needs `erw [funext …]` (instance terms
  under the lintegral are not syntactically equal) and a closing `rfl`.

## Result

File `Surgery/Topology/HistoryHorizonExtension.lean`, 414 lines. `lean` on the file: 0 errors,
0 warnings, 0 infos. `#lint` (Batteries default set): 0 errors in 23 declarations.
`#print axioms` (removed): every public theorem depends on at most `propext, Classical.choice,
Quot.sound` (`reducedVolume_extendHorizon`: none); no `sorryAx`.

Delivered (namespace `RetainedCoreHistory`): `exists_extendHorizon_gt`, `reducedVolume_extendHorizon`,
`stageMetric_extendHorizon`, `isParabolicallyRmControlledBall_extendHorizon`,
`lt_stageEndTime_extendHorizon`, `mem_Icc_of_mem_stageDomain'`, `stageDomain_extendHorizon`,
`mem_Ico_extendHorizon_of_mem_stageDomain`; supporting public lemmas `stageEndTime_extendHorizon_last`,
`stageEndTime_extendHorizon_castSucc`, `activeStage_extendHorizon`,
`stageMetric_extendHorizon_last_of_mem_Icc` (the name `stageMetric_extendHorizon_last` is taken in
`TracedRegion.lean`), `regularizedStageStart_extendHorizon`,
`stageRegularizedExtendedAction_extendHorizon`, `regularizedExtendedAction_extendHorizon`,
`regularizedActionValues_extendHorizon`, `regularizedCost_extendHorizon`,
`regularizedDensity_extendHorizon`, `regularMinimizerEndpoints_extendHorizon`.

Deviations from §5.4: one, cosmetic. In `exists_extendHorizon_gt` the two Prop binders are anonymous
(`(_ : H.horizon < T')`, `(_ : G.flow.base.metric … = …)`) instead of `hT'`/`hG`: named unused
binders trip the unused-variables linter. The elaborated type is identical, and §5.5's
`obtain ⟨T', hT', G, hG, hagree⟩` is unaffected. All other statements are verbatim.
`mem_Icc_of_mem_stageDomain'` keeps the design's primed name because the consumer calls it; no
unprimed version exists, so the lead may rename it.
