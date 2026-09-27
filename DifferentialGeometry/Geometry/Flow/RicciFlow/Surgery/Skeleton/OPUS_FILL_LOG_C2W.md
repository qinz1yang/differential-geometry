# Lane C2W: next C2 wave of DESIGN_C2_ASSEMBLY (H7b+, Gauss/SB3, T9)

2026-09-26. Worker in `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf`). Read-only
compiles (`lake env lean` equivalent with the lakefile options), scratch modules under the session
scratchpad `c2w/`. No lake build, no git writes, root aggregate untouched. New files only.

## Start (11:40 PDT)

Read: pc3 AGENTS.md (zero comments/docstrings, no header, no module docstring), DESIGN_C2_ASSEMBLY
(all), FILL_QUEUE row 22 bricks, FREE_INPUTS C2 row, logs C2W1, C2M, C2E, H7B, G1B, G1C.

Status of §6 bricks (queue row 22 + logs): committed G7, G7′, TailG, SB1/SB2 (`SeamBase`), X1–X3,
E2a, E, CF, C9, H7c, M1/M3/M (ACC11 building now); H7b uncommitted (17 files, H7F verifying).
Remaining in the wave table outside H8/H9: **H7b+**, **SB3/Gauss**, **T9**. No other lane owns them
(queue: "T9/H7b+/SB3/H8/H9 pending"). CF is delivered (ACC8), SB1–SB2 are `SeamBase`.

Bricks taken and why unblocked:
- H7b+ `historyReducedJacobian_le_of_le`: suppliers H7b (uncommitted, consumed via the H7F scratch
  oleans), H7a, H5 truncation, E's closed-start construction (committed), G1b/E2a (committed).
- SB3/Gauss `historyReducedJacobian_le_gaussian`: suppliers H7c (committed), H7b+ (this lane),
  SB1 seam-base window (committed).
- T9 `lintegral_image_historyMinDomain_tail_le`: suppliers G7 (committed), M (ACC11), E
  (committed), Gauss (this lane).

Key structural fact: `stageDomain` is `Ico` (closed only for the last stage), so stage domains are
disjoint and `k` in H7b+ is `historyStage T v₁`; there is no closed-END case, only closed starts
(`T - v² = time k`). H7b+ therefore reduces to left continuity of `historyReducedJacobianAlong` at a
closed-start endpoint plus the H7b pairwise lemma on non-seam parameters and truncation.

## Progress 1 (12:25 PDT) — H7b+ proved (scratch compile clean)

Compile route: scratch modules `C2w.*` under the session scratchpad `c2w/` (script `c2w/sc.sh`),
LEAN_PATH = `c2w/olean ; h7f/olean (the H7F lane's scratch oleans of the 17 H7b files, imported as
H7f.*) ; pc3 build`. Lakefile options passed as `-D`.

- `Surgery/Topology/HistoryLGeometry/JacobianClosedStart.lean` (new): left continuity of
  `historyReducedJacobianAlong` at a closed-start endpoint.
  - private `continuousWithinAt_paramDensity_of_metricSmoothUpTo`: for a jointly `C^∞` family
    `β` and a metric family with `MetricSmoothUpTo g J`, `s ↦ paramDensity (g (τ s)) (β (·, s)) Z₀`
    is continuous within any set on which `τ ∈ J` (one-sided at a closed start). Proof: fixed chart
    at `β (Z₀, s₀)`, `paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt`, chart Gram
    through the `MetricSmoothUpTo` matrix `A` (`inner_chartVector_sum`, private in
    `SlabJointSmoothness`, opened).
  - private `exists_family_of_closedStart`: joint `C^∞` family of the stage-`first` tail up to a
    closed start. COPY of the construction inside E's private `exists_package_of_closedStart`
    (`ExponentialClosedStart.lean` l.683–1024, action parts removed); deferred merge: E could export
    the family and its package lemma become a corollary.
  - private `historyLAction_truncate_eq`, `continuousWithinAt_sum_integral_historyLCurve`: the
    truncated action as an integral of the level-`w` curve's Lagrangian; continuity in the end
    parameter from integrability (M3 `intervalIntegrable_stageRegularizedLagrangian_historyLCurve`).
  - public `continuousWithinAt_historyReducedJacobianAlong_of_closedStart` (no minimizer needed)
    and `continuousWithinAt_historyReducedJacobianAlong_of_mem_historyMinDomain` (both cases; the
    interior case is H7b's `continuousWithinAt_historyReducedJacobianAlong`).
- `Surgery/Topology/HistoryLGeometry/JacobianComparison.lean` (new):
  - `historyReducedJacobianAlong_antitoneOn`: `AntitoneOn (historyReducedJacobianAlong Z) (Ioc 0 w)`
    for `Z ∈ historyMinDomain` (DESIGN_22 §4's original statement: seam parameters, closed-start
    end, any base time). Proof: pairwise H7b at non-seam parameters after truncation
    (`mem_historyMinDomain_of_le`), left limits at both ends from the closed-start/interior
    continuity, finitely many seam parameters avoided eventually in `𝓝[<]`.
  - H7b+ `historyReducedJacobian_le_of_le` (DESIGN_C2_ASSEMBLY §5.2). DEVIATION: the hypothesis
    `hT : T ∈ Ico (H.time last) (H.stageEndTime last)` is dropped — it is unused (the unused-variables
    linter rejects it) and the conclusion holds for every base time. Binder order otherwise
    verbatim: `hfloor hfk hkl hv₁ h12 hk Z hZ`; H8's call in §5.5 drops the `hT` argument.

## Progress 2 (12:48 PDT) — SB3/Gauss and T9 proved; DONE

- `Surgery/Topology/HistoryLGeometry/SeamBaseJacobian.lean` (new, SB3 = H7c on the glued seam base
  window). Seam base `T = time i.succ`, window `W : LWindow i.castSucc i.succ T`, `W.a = 0`:
  - private `metric_eq_localPullMetric_of_seamBase`: `W.S.base.metric T` is the pullback of the
    new stage's initial metric through `W.f succ`. Proof: left limit through the `castSucc` piece
    (`W.metric`), the incoming metric tends to `terminal.metric` (`closedSolution_isSolutionOn ⊤`,
    `coeff_cont` at the terminal time), then the survivor chart isometry
    (`RegularCrossing.exists_survivor_partialDiffeomorph`, `SurvivorChartMetric`) and
    `mfderiv_partialDiffeomorph_apply_eq_of_regularCrossing` (Seam).
  - private seam versions of H7c's BaseWindow lemmas (history geodesic/initial vector of
    `W.f j ∘ lRegularizedCurve`, action = `lRegularizedAction` (the `succ` piece is `[0,0]`),
    density/source quotient, minimality through `LWindow.lRegularizedAction_le_of_regularizedCost_eq`
    with the crossing node data, `lMinDomain` membership). Two H7c private lemmas that only used
    `W.S` (`exists_nhds_lRegularizedDomain`, `exists_contMDiffOn_lRegularizedCurve`) are copied for
    an arbitrary window (`…_of_window`); deferred merge: generalize H7c's BaseWindow section to
    `LWindow lo last T` and delete the copies.
  - public `exists_pos_historyReducedJacobian_le_gaussian_of_time_eq`: at a seam base, for
    `Z₀ ∈ historyMinDomain` there are `k ≤ last` and `0 < δ ≤ v₂` with `T - v² ∈ stageDomain k` and
    `ℓJ_k(v) ≤ π^{-3/2} e^{-g_T(Z₀,Z₀)}` for `v ∈ (0, δ)`.
- `Surgery/Topology/HistoryLGeometry/JacobianGaussian.lean` (new): Gauss
  `historyReducedJacobian_le_gaussian` (design §5.2). Proof: small-`v` Gaussian bound (H7c when
  `time last < T`, SB3 at a seam base) + H7b+. DEVIATION: `hT` dropped (unused: `T ∈ stageDomain
  last` already follows from `Z`); arguments `hfloor hv Z hZ`.
- `Surgery/Topology/HistoryLGeometry/ReducedVolumeTail.lean` (new): T9
  `lintegral_image_historyMinDomain_tail_le`, statement VERBATIM (design §5.2). Proof: E's open
  package, M measurability, G7 on `K = historyMinDomain ∩ {R < √g(Z,Z)}`, pointwise
  `ofReal J · dens = ofReal src · ofReal ℓJ ≤ ofReal (src · Gauss)`. File-local `borel` instances
  on stage carriers and on `ThreeSpace` (as G7/TailG/C9).

Checks (all scratch, lakefile options, full Mathlib standard linter set):
- Compile: all 5 files 0 errors, 0 warnings. `#lint` on scratch copies: all passed
  (6 + 6 + 19 + 2 + 5 declarations).
- Axioms (probe, removed from tree — the probe lives in the scratchpad only):
  `continuousWithinAt_historyReducedJacobianAlong_of_closedStart`,
  `continuousWithinAt_historyReducedJacobianAlong_of_mem_historyMinDomain`,
  `historyReducedJacobianAlong_antitoneOn`, `historyReducedJacobian_le_of_le`,
  `exists_pos_historyReducedJacobian_le_gaussian_of_time_eq`, `historyReducedJacobian_le_gaussian`,
  `lintegral_image_historyMinDomain_tail_le`: all `[propext, Classical.choice, Quot.sound]`.
- Public names grepped library-wide: no clash.
- No comments/docstrings, no sorry/axiom/nolint/heartbeat options; no line over 100 characters
  except `open private … from <module>` lines (module path unbreakable, as in the siblings).
- Assembly probe (scratch only, NOT a delivery): DESIGN_C2_ASSEMBLY §5.5's H8 chain
  (`lintegral_image_historyMinDomain_le_of_lt`, `reducedVolume_le_of_lt_of_mem_Ico`, the
  `HistoryReducedVolumeMonotone P₀` proof) and H9 proof (`HistoryReducedVolumeLocalUpperBound P₀`)
  compile verbatim against the delivered bricks with exactly two edits: the H7b+ call drops `hT`,
  and `mem_Icc_of_mem_stageDomain'` is spelled `mem_Icc_zero_horizon_of_mem_stageDomain` (X's
  rename). Both leaves' axioms: `[propext, Classical.choice, Quot.sound]`. T9 composes with TailG
  (`(T9 …).trans (htail g p)`) under the file-local `borel` instances.

Files (lines): JacobianClosedStart 642, JacobianComparison 118, SeamBaseJacobian 652,
JacobianGaussian 70, ReducedVolumeTail 117 (total 1599).
Root-aggregate registration (lead): the 5 modules, after the 17 H7b modules; import order
JacobianClosedStart (needs H7b `JacobianEndpoint`) → JacobianComparison (needs `JacobianMonotone`)
→ SeamBaseJacobian (independent of H7b) → JacobianGaussian → ReducedVolumeTail.
What H8/H9 still lack: nothing mathematical — only commits of the H7b files and of these five,
plus the two call-site edits above.
