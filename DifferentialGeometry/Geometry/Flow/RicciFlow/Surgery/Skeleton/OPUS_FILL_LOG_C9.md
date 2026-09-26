# OPUS fill log: brick C9 `exists_lintegral_image_historyMinDomain_core_le`

2026-09-26. Worker C9, worktree `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf`).
No `lake build`, no git writes, `DifferentialGeometry.lean` untouched, no committed file modified.
Target file (new): `Surgery/Topology/HistoryLGeometry/CoreIntegralBound.lean`.

## Proof plan

Fix `R`. G6 (`exists_pos_lRegularizedCurve_mem_ball_of_parabolic_rm_bound R`) gives `σ₆ ∈ (0, 1]`.
Export `σ := σ₆ / 2`, so `0 < σ ≤ 1/2 ≤ 1` and `v := σ r = σ₆ (r/2) ≤ r/2 < r`.

Given `H t p r B hball ht hfloor hle`:
1. CF gives `a = t − r²`, `t₁ > t`, `U = B(p, r)`, `f`, `S` on `closed a t₁`, stage metrics
   `S(τ) = localPull(stageMetric j τ, f j)`, `r⁴|Rm|² ≤ 1` on `[a, t] × U`, `S(t) = g_t|U`, and a
   compact `K` with `val '' K = closedBall(p, r/2)`.
2. G6 is applied to the NEW flow `S` with radius `r/2` (base `t ∈ Ioo a t₁ = D.regular`;
   `{d_U(pU, ·) ≤ r/4}` is closed and inside `K` because `d_stage ≤ d_U`,
   `riemannianEDistOf_le_restrictOpen`). For `√g(Z,Z) ≤ R` it gives `v ∈ lRegularizedDomain S t pU Z`.
3. The window `W` (`X = U`, `a = 0`, `b = v`, `lo = first`, `hi = last`, `f` reindexed from CF) makes
   `β j := f j ∘ lRegularizedCurve S t pU Z` a history L-geodesic with initial vector `Z`
   (`mfderiv_subtype_val_apply`). H3a uniqueness
   (`IsHistoryLGeodesicOn.eqOn_of_hasHistoryLInitialVector`) identifies the `historyMinDomain`
   witness `α₀` with `β` on every stage piece. Hence `historyLExp Z = f first (γ v)`.
4. Density: every competitor action `A ≥ cost(q) = extAction(α₀)`. On each piece the scalar
   curvature along `α₀ = f j ∘ γ` equals that of `S` (`metricScalarAt_localPull`), and
   `|R_S| ≤ 9/r²` (`scalar_abs_le_div_sq_of_rm_bound`, `n = 3`). Re-base the extended action's
   floor to `C = 9/r²` (`stageRegularizedExtendedAction_congr_scalar_lower_bound`), bound below by
   `∫ −2C s²`, telescope with `sum_regularizedStage_sub`: `cost ≥ −6v³/r²`. So
   `dens(q) ≤ (4π)^{-3/2} e^{3} / v³ ≤ (4π)^{-3/2} e^{9}/v³`.
5. Volume: image `⊆ f first '' univ`; `μ_first(f '' univ) = μ_{S(t−v²)}(U)` (injective local
   isometry, `riemannianVolumeMeasure_image_eq_of_injective_local_isometry`);
   G8 on `[t − r², t]`: `≤ e^{27} μ_{S(t)}(U)`; `S(t) = g_t|U` and
   `riemannianVolumeMeasure_restrictOpen_preimage_of_subset`: `= vol_t(B(p, r))`.
   A private lemma bounds `∫⁻ over a (possibly non-measurable) set` by `sup · μ(set)`.

Constant: `e^{9} · e^{27} = e^{36}`.  `0 < σ` and `σ ≤ 1` from G6's `σ₆`.
Note: G6's `r/4` confinement is not needed; the volume bound uses all of `U`.

## Result

- New file `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/HistoryLGeometry/CoreIntegralBound.lean`
  (393 lines). No header or module docstring, following the pc3 AGENTS.md and the sibling files.
  Namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory`.
- Public theorem `exists_lintegral_image_historyMinDomain_core_le`. Its statement is byte-identical
  to DESIGN_C2_ASSEMBLY.md §5.3 (checked with `diff`). Proved with no `sorry`.
- Imports: CF (`HistoryParabolicBallForwardFlow`, olean current as of 09:39), `HistoryLGeometry.MinDomain`,
  `HistoryReducedDensity`, G6 `Perelman/LGeometry/Ray/ParabolicBallRange`, G8
  `Perelman/Noncollapsing/VolumeDistortion`, `Geometry/Measure/LocalIsometry`,
  `Geometry/Curvature/Bounds/ScalarNorm`, `Perelman/LGeometry/Geodesic/WindowSolutionMap`.
  No committed file was modified. The file is not yet registered in `DifferentialGeometry.lean`
  (the acceptance lane owns that file).
- Private helpers:
  - `setLIntegral_le_mul_of_forall_mem_le`: `∫⁻ x in s, f ≤ c · μ s` when `f ≤ c` on `s`, for any
    set `s`, measurable or not (simple-function argument; a measurable set disjoint from `s` is
    `μ|s`-null).
  - `regularizedDensity_historyLExp_le_of_scalar_lower`: if `Z ∈ historyMinDomain` and
    `R ≥ −C` along `historyLCurve Z` on every stage piece, then
    `dens(historyLExp Z) ≤ exp(C v²/3 − (3/2) log v² − (3/2) log 4π)`.
  - `exists_mem_historyLExpDomain_eqOn_of_commonFlow`: a common flow on `X` with local
    diffeomorphisms `f j`, regular crossings and stage-metric pullbacks on the pieces, together with
    `v ∈ lRegularizedDomain S T x Zx`, puts `Z = df(Zx)` in `historyLExpDomain`, and
    `historyLCurve Z j = f j ∘ lRegularizedCurve S T x Zx` on each piece. It builds one `LWindow`
    with `a = 0`, `b = v` and uses H3a uniqueness.
  - `exp_density_exponent_le`: the scalar exponent inequality.
- Compile: `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
  -Dweak.linter.mathlibStandardSet=true` on the file in place gives 0 errors and 0 warnings.
  Scratch copy with `#lint`: 0 errors in 7 declarations, 14 linters.
- `#print axioms` (scratch copy only, then deleted): `[propext, Classical.choice, Quot.sound]`.

## Deviations

- None in the statement.
- Constant route: the scalar bound is `|R| ≤ n²/r² = 9/r²` (`scalar_abs_le_div_sq_of_rm_bound`),
  not the design's `R ≥ −27/r²`. This gives `cost ≥ −6v³/r²` and a density exponent of at most
  `3·σ² ≤ 3/4`. That is bounded by `9` and then multiplied by G8's `e^{27}`, so the stated
  `e^{36}` holds with room to spare.
- `σ := σ₆/2`, where σ₆ comes from G6. G6 is applied with radius `r/2`, so `v = σr ≤ r/2 < r`.
  This keeps the window's closed end `t − v²` strictly inside `D.regular = Ioo a t₁`: `LWindow.regular`
  needs `Icc 0 v`, and `σ = 1` would put `t − v²` at `a`.
- G6's `r/4` confinement is unused. The volume step uses all of `U`: the image lies in
  `f first '' univ`, and `μ_{S(t)}(U) = vol_t(B(p, r))`.
- Deferred-merge candidate: `exists_mem_historyLExpDomain_eqOn_of_commonFlow` is a reusable
  multi-stage generalisation of JacobianLimit's private single-stage `historyLCurve_eqOn_window`.
  It could be promoted to a public lemma in a `HistoryLGeometry` home later.
