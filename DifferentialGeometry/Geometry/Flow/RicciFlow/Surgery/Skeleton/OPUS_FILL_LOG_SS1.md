# OPUS_FILL_LOG_SS1 — small-scale bricks S3, S2a/S2 (+twin), S1 (+twin), R2, R3, R4

Design: `Skeleton/DESIGN_SMALLSCALE.md`. Worktree `D:\differential-geometry-pc3`, branch
`codex/pc-target-c-psf`. New files only; no builds, no git writes; compiles by `lake env lean`
(2 threads) or the scratch-module pattern.

## 2026-09-26

- 18:30Z start. ACC8 cascade (R0's `MetricComparison` edit, ~1212 modules) is rewriting oleans;
  `lake env lean` fails on missing oleans while it runs. Writing sources meanwhile.
- R3 + R4: `Surgery/Topology/StageComponentSimplyConnected.lean` written (R4 body verbatim from
  the design; R3 via `Homeomorph.setCongr` and `HomotopyEquiv.simplyConnectedSpace`).
- Scratch route: `C:\Users\liao9\AppData\Local\Temp\claude\ss1\scomp.sh` copies a repo file to
  `ss1/src/SS1/...`, rewrites imports of uncommitted modules to root `SS1`, compiles with
  `lean -DmaxSynthPendingDepth=3 -Dweak.linter.mathlibStandardSet=true` (lakefile options) and
  `LEAN_PATH = ss1/olean ; lake env`. (Mixing a scratch `DifferentialGeometry` root with the repo's
  fails: Lean resolves a package root to the first search-path entry containing it.)
- S3 (~19:00Z): general brick `Geometry/Comparison/Volume/Bishop/LocalBallRatio.lean`
  (namespace `…Riemannian.VolumeComparison`): for a complete metric on any manifold,
  `riemannianBallOf_volume_ratio_ge_of_ricci_lower` (Ric ≥ −(n−1)q²g on `B(p,R)` ⇒
  `e^{−q(n−1)R}(r/2R)ⁿ·vol B(p,R) ≤ vol B(p,r)`) and `…_of_ricci_nonneg` (the `q = 0` case,
  exact factor `(r/R)ⁿ`). Stage corollary `Surgery/Topology/StageBallVolumeRatio.lean`:
  `exists_riemannianVolumeMeasure_ball_ge_of_rm_le`, statement verbatim, `c = e^{−6}/8`
  (Ric ≥ −9R⁻²g from `ricciLowerAt_of_rm`, applied with the cruder `q = 3/R`, `2q² = 18/R²`, so
  `q(n−1)R = 6`). Compiles clean.
- R3/R4 compile clean (`StageComponentSimplyConnected.lean`).
- S2a/S2 (~19:20Z): `Surgery/Topology/CapWindowPointScalar.lean`.
  - S2a event level `exists_presented_cap_window_scalar_lower_bound Dcap Dstar (hD : Dcap + 1 < Dstar)`:
    `∃ ε₀ > 0`, every canonical-window presented cap with `Dstar ≤ D`, `ε ≤ ε₀`, `2 ≤ m` has
    `scale/2 ≤ R(outputMetric)(window x)` for `‖x‖ < Dcap + 1`. So **`Cw = 2`** (the window
    scalar lemma gives `1/2 < R`). History form `RetainedCoreHistory.exists_window_scalar_lower_bound`
    gives exactly `hwinScale` with `Cw = 2` from `hcan`, `Dstar ≤ p.modelRadius`,
    `p.modelAccuracy ≤ ε₀`, `2 ≤ p.modelOrder`.
  - Deviation (constants only): S2a needs `Dcap + 1 < Dstar ≤ p.modelRadius`, because the window
    closeness is only known on `‖y‖ < modelRadius` and `hwinScale` asks for `‖x‖ < Dcap + 1`.
    Leaf wiring: export the leaf's `Dcap` as `Dcap_cw + 2` (any value `> Dcap_cw + 1`) and use
    `Dstar := Dcap_cw + 2`; S1's `hDstar/hDmodel` accept it.
  - S2 `not_capWindowPoint_of_scalar_le` statement verbatim; twin
    `not_capWindowPoint_of_scalar_le_of_activeStage_eq_last` (replaces `i, hi, hcurrent` by
    `h : time last < horizon`, `hlastA`, `hfinal` for the restricted final slab). Both through one
    private core; no positivity of `M` needed (the proof runs the reciprocal bound at
    `q = max M (scale/(2(Cw+Ctime θcap)))`). Compiles clean.
- S1 (~19:45Z): `Surgery/Topology/BackwardTraceDistortionThreshold.lean`.
  `RetainedCoreHistory.exists_isParabolicallyRmControlledBall_or_capWindowPoint_of_scalar_le`
  (statement verbatim) and twin `…_of_scalar_le_of_activeStage_eq_last` (hypotheses of
  `BackwardTraceDistortionTerminal.lean:517` with `hqR, hR, hu` replaced by `hqM, hM, hyM, hu`).
  Proof: the two existing proofs with `R(y)` replaced by the threshold `M` (radius `c/√M`, window
  `t − u = c²/M`), shared arithmetic in a private lemma.
  - Needed generalisation: the ball scalar bound had to hold without `0 < R(y)` (the low case has
    only `R(y) ≤ M`; `R` may be negative). New
    `Perelman.CanonicalNeighborhood.scalar_le_four_mul_of_gradient_bound` (any `N > 0` with
    `R(x) ≤ N`, `qcan ≤ N`, `Cgrad·r·√N ≤ 1/4` ⇒ `R ≤ 4N` on `B̄(x,r)`); it is the proof of
    `scalar_le_four_mul_max_of_gradient_bound` (`SlabGradientScalarControl.lean:25`) with
    `N := max R(x) qcan` generalised. Follow-up for the lead (not done: that file is not mine):
    re-derive the old lemma from the new one to remove the duplicated proof body.
  - Compiles clean (standard linter set on).
- Lead message (~19:50Z): H10 digest (`Surgery/consult/H10-smallscale-s4-review-digest.md`) is
  binding; R2 must not assume `ε < 1/11`; add S4 and S4′ after the current bricks.
- R2 (~20:10Z): `Perelman/CanonicalNeighborhood/SpatialRoundComponentBallVolume.lean`
  (namespace `…FiniteHorn`). **Statement changed (lead-directed):**
  ```
  theorem exists_ball_volume_of_spatialRoundComponent (C1 C2 : ℝ) :
      ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier} {eps : ℝ}
        (W : SpatialCanonicalWitness g eps C1 C2 x), W.domain.carrier = connectedComponent x →
        SpatialRoundComponent g eps x W.domain.carrier →
        SimplyConnectedSpace (connectedComponent x) → ∀ r : ℝ, 0 < r →
        r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
        ENNReal.ofReal (κ * r ^ 3) ≤ riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r)
  ```
  Reason: without `ε < 1/11` the round datum alone gives no curvature bound on `U` (its
  `comparison` is `ε`-close only), so the Ricci lower bound comes from the witness's `rm_bound`;
  the witness is exactly what S4′ holds in the `.round whole data` case (`whole`, `data` are the
  two extra arguments). `κ` depends on `(C1, C2)` only, not on `eps`.
  Proof: `U = W.domain = connectedComponent x`; `r ≤ 3Q^{-1/2}` (new public
  `sqrt_scalarAt_mul_le_three_of_rm_le`, from `scalar_abs_le_rm`); `L = 3A·Q^{-1/2}` with
  `A = max C1 1` covers `r` and `U ⊆ B(x, 2·radius)`; `B(x,L) ⊆ connectedComponent x`
  (`edistOf_ball_subset_connCompOpen`); `Ric ≥ −9BQ·g` on `B(x,L)` from `rm_bound`
  (`B = max C2 1`), fed as `q = 3√(BQ)` to the general BG `LocalBallRatio`; R1 constant
  `4√3π·Q^{-3/2}`. **κ = e^{−18A√B}·4√3π/(216A³).** Compiles clean.
- S4 + S4′ (~21:30Z): `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessBallVolume.lean`
  (namespace `…FiniteHorn`). `exists_ball_volume_of_spatialCanonicalWitness` (S4) and
  `exists_ball_volume_of_spatialCanonicalWitness_of_simplyConnected` (S4′), statements verbatim
  (checked by `example … := thm` against the design text in a scratch probe).
  - neck: `BallVolume.lean:286`.
  - positive: `B(x,L) ⊆ U = connectedComponent x`, `L = 3A·Q^{-1/2}` (`A = max C1 1`),
    `Ric ≥ 0` from `SecLower` via `ricci_lower_of_sectionalBoundedBelowAt`, BG with `Ric ≥ 0`
    (`LocalBallRatio`, exact factor `(r/L)³`), `vol U ≥ C2⁻¹Q^{-3/2}`:
    **κ_pos = 1/(27A³B)** (`B = max C2 1`), as in H10.
  - cap (route differs from H10's last-crossing, same ingredients otherwise; reason: avoids a
    chart-length lower bound for curves crossing the neck): `D := inf_{tube} d(x,·)` (in
    `[10⁴Q^{-1/2}, 2·radius]`); **first exit**: `B(x,D)` is path connected, meets `interior U`, and
    misses `frontier U ⊆ tube` (`outer_boundary`, `tube_eq`), so `B(x,D) ⊆ U`; pick `w ∈ tube`
    with `d(x,w) < D + δ`, `δ = (4√Q_v)⁻¹`, and on a near-minimizing curve (Mathlib
    `exists_lt_of_riemannianEDist_lt`, IVT, `pathELength_add`) a point `w'` with
    `d(x,w') = D − s`, `d(w',w) < s + δ ≤ (2√Q_v)⁻¹`, `s = min(δ, D/2)`; then `B(w',s) ⊆ B(x,D)`;
    `w = nk.map z₀`, `z₀ ∈ S²×[0,1]`, and the chart capture at `z₀` (radius 1, cross-model capture
    lemma) puts `w' = nk.map z'` with `|z'₂| ≤ 2`; `BallVolume.lean:150` at normalized radius
    `√Q_v·s ≤ 1/4` gives `vol B(w',s) ≥ ν s³`; general BG with `Ric ≥ −9BQ·g` on `B(x,D)` from
    `rm_bound` (no S3 call at `D + s`). `Q_v ≤ BQ` (`scalar_bounds`, `v ∈ tube ⊆ U`), `D√Q ≤ 2A`.
    **κ_cap = e^{−12A√B}·ν·σ³/(64A³)**, `σ = min((4√B)⁻¹, 5000)`.
  - round: S4 excludes it (`requiresVolume = False`); S4′ uses R2 (no `ε < 1/11`).
  - S4 κ = `min κ_neck (min κ_pos κ_cap)`; S4′ κ = `min κ_S4 κ_R2`.
- Verification (~21:40Z): all 7 files compile clean through the scratch route with the lakefile
  options (0 errors, 0 warnings, 0 infos); `#lint in SS1` (scratch copies, 14 linters): 0 errors in
  69 declarations. `#print axioms` for every public theorem: `[propext, Classical.choice,
  Quot.sound]`, no `sorryAx` (probe removed). Public names grep-unique. No comments/docstrings,
  no `sorry`/`nolint`/option overrides, LF line endings.
- Root aggregate (not touched): register, in dependency order,
  `Geometry.Comparison.Volume.Bishop.LocalBallRatio`,
  `…Surgery.Topology.StageComponentSimplyConnected`, `…Surgery.Topology.StageBallVolumeRatio`,
  `…Surgery.Topology.CapWindowPointScalar`, `…Surgery.Topology.BackwardTraceDistortionThreshold`,
  `…Perelman.CanonicalNeighborhood.SpatialRoundComponentBallVolume` (needs R0's uncommitted
  `SpatialRoundComponentVolume` + `SimplyConnectedSpaceForm` + `BallVolumeBound`),
  `…Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume`.
