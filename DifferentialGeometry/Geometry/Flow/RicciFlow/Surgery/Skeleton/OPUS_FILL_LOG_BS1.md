# OPUS fill log BS1 (bricks BS1, BS3, BS4, BS2, BS5, BS7 of DESIGN_BASESLICE.md), 2026-09-26

Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf`. New files only; no `lake build`, no git
writes, root aggregate untouched. Paths relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`.

## Files

- `Surgery/Topology/CapWindowPointTimeSlack.lean`: BS3 `RetainedCoreHistory.CapWindowPoint.of_le_time`,
  BS4 `RetainedCoreHistory.exists_forall_neck_scale_le`.
- `Surgery/Topology/SlabTimeWindowContinuity.lean`: BS1
  `OrientedThreeStage.IncomingSlab.exists_forall_Icc_scalar_riemannNorm_metric_close` (plus one private helper,
  uniform-in-space time continuity of a jointly continuous function via the compact tube lemma).
- `Surgery/Topology/SliverWindowData.lean`: BS2 `OrientedThreeStage.IncomingSlab.exists_sliver_data`.
- `Surgery/Topology/SliceBallBoundTransfer.lean`: BS5 support, `exists_mem_Ioo_scalar_metric_close` (one interior
  slice `σ` close to `t₀`) and `exists_earlier_slice_scalar_ball_transfer` (all numeric input transfers at `σ` and
  the ball/scalar transfer `σ → t₀ → t`).
- `Surgery/Topology/BoundedCurvatureAtDistanceSliver.lean`: BS5 event and terminal forms.
- `Surgery/Topology/InitialSlabScalarWindow.lean`: BS7 `exists_forall_Icc_scalar_le_at_initial_slab_start`.

## Timeline

- 16:10Z BS3/BS4 compiled clean against the shared build (`lake env lean`, 2 threads), statements §2 verbatim.
- BS4: `TubeSystem.Boundary = Index × Bool` with `[Fintype Index]` (`CutCap.lean:26–49`), so
  `RetainedBoundaryIndex` (a subtype) is `Finite`; the first choice of §3 works (finite range of the scale function
  over the sigma type `Σ i, RetainedBoundaryIndex`, `S := max (sup) 1`). Fallback NOT used.
- 16:25Z BS1 compiled clean. Proof: `IsCompact.eventually_forall_of_forall_eventually` on the subtype
  `Ico a s × Carrier` (no uniform structure on the carrier needed) for `R` (`G.equation.scalarCont`) and `|Rm|`
  (`continuousOn_riemannNorm`); the metric clause from `metric_inner_exp_bounds_of_curvature_bound` with the
  `|Rm|` bound on `Icc a ((t₀+s)/2)` (`exists_forall_Icc_riemannNorm_le`) and `δ ≤ log(1+ζ)/(36(K+1))`.
  BS1′ skipped (optional; not consumed).
- 16:34Z ACC8's build killed/restarted a cascade from `MetricComparison`; `Analysis/Parabolic/Dirichlet/Energy.olean`
  and others missing in the shared build. Switched to a private olean mirror `E:\bs1-mirror\lean` (real dirs,
  hard links of every shared `.olean`; the 1236 closure modules that depend on `MetricComparison`, i.e. the ones the
  cascade may rewrite, are COPIED, not linked, so the running build is never blocked by a mapped link). Missing
  `Energy` and the 12 uncommitted B3F modules of the `…SliceEvent` closure are compiled into the mirror with
  `lean -o`, lakefile options passed by `-D` (incl. `weak.linter.mathlibStandardSet=true`,
  `maxSynthPendingDepth=3`).
- 16:36Z lead message: BS5 added (review H8 digest `Surgery/consult/H8-baseslice-bs5-review-digest.md`, corrections
  binding). Constants as the digest: `A_B = 2√e·A`, `Cq_B = 2Cq`, `θ_B = θ/2`, `Q = 2Q_B + 1`, `Λ = 4Λ_B`;
  `R/2 ≤ Rσ ≤ 3R/2`, `σ ≥ t₀/2`, `gσ ≤ 2g_{t₀}`, ball `B_t ⊆ B_{t₀}(√e) ⊆ B_σ(√2·√e) ⊆ B_σ(2√e·A/√Rσ)`.
  `Λ ≤ R·t₀` stays a hypothesis. Terminal form keeps `PhiAlmostNonnegative` and `TerminalNoncollapsedBefore`
  (the latter restricted to `σ` inline: `fun T hT hTs hTle => hnc T hT hTs (hTle.trans hσt₀.le)`).
- BS2 (correction (2) of H8): the metric `e`-comparison in both directions is part of BS2's conclusion, built into
  `η` from BS1's metric clause with `ζ' = min ζ (e − 1)` (so `1 + ζ' ≤ e`), independently of the scalar closeness.
- Mirror compile pitfalls (for the next lane): the vendored `External/` modules need `.olean.server` and
  `.olean.private` links too; in bash, `"E:\…\${f}"` escapes the `$` (use forward slashes).
- 16:50–17:05Z all six files compiled clean in the mirror with the lakefile options (exit 0, no output, i.e. no
  warnings/linter output): BS3/BS4 42 s, BS1 49 s, transfer 50 s, BS2 38 s, BS7 42 s, BS5 51 s. The 12 B3F modules and
  `Energy` also compiled clean into the mirror (41–67 s each).
- BS2 first compile: one `⟨le_rfl, hη.le⟩` fixed to `⟨le_rfl, by linarith⟩`.
- BS5 compiled first try; statements are §2 verbatim (event and terminal). The only added hypothesis anywhere is
  `0 < A` in the support lemma `exists_earlier_slice_scalar_ball_transfer` (BS5 has `hA`).
- `#print axioms` (probe outside the tree, deleted): all nine public declarations
  `[propext, Classical.choice, Quot.sound]`. `#lint` (14 linters) and `#lint only unusedArguments`: 0 errors in
  every file. New public names unique library-wide (grep). `git diff --check` clean. Mirror `E:\bs1-mirror` removed
  (shared build olean count unchanged, 11443), probes removed.

## Deviations per brick

- BS1: none (statement §2 verbatim). BS1′ not done (optional).
- BS2: none (verbatim). The metric `e`-comparison is inside `η` (H8 correction (2)).
- BS3, BS4: none (verbatim). BS4 uses the finiteness route, not the fallback.
- BS5 (event + terminal): none (verbatim, H8 constants). `Λ ≤ R·t₀` kept as a hypothesis.
- BS7: §2 gave only a comment sketch; stated as
  `exists_forall_Icc_scalar_le_at_initial_slab_start (P₀ g₀) : ∃ Q₀, 0 < Q₀ ∧ ∀ H : ObservedHistory,
  InitialIdentification P₀ g₀ H → ∀ {s} (G : (H.stage 0).IncomingSlab (H.time 0) s), G.metric (H.time 0) =
  H.initialMetric 0 → ∃ η, 0 < η ∧ H.time 0 + η < s ∧ ∀ t ∈ Icc (H.time 0) (H.time 0 + η), ∀ y, R t y ≤ Q₀ + 1`
  (the sketch plus the harmless extra conclusion `H.time 0 + η < s`; `Q₀` is the one of
  `exists_scalar_lt_at_initial_slab_start`).

## Wiring (not done here; root aggregate untouched)

Six new leaf modules to register in `DifferentialGeometry.lean`: `Surgery/Topology/{CapWindowPointTimeSlack,
SlabTimeWindowContinuity, SliverWindowData, SliceBallBoundTransfer, BoundedCurvatureAtDistanceSliver,
InitialSlabScalarWindow}`. `BoundedCurvatureAtDistanceSliver` needs the uncommitted B3F closure (12 modules ending in
`BoundedCurvatureAtDistanceSliceEvent`). `BoundedCurvatureAtDistanceAfterEvent.lean` (BS6 lane) already imports
`CapWindowPointTimeSlack`.
