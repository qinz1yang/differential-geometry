# B6g3 — DESIGN_B6D_GLUE brick B7 (B6b' exports: time-Lipschitz, scalar bound, e^2 lower bound), 2026-09-26

- Start. Read AGENTS.md (pc3), DESIGN_B6D_GLUE.md (§0 F-d/F-e/F-h, §1, §2 B7/B8/B11), H7 digest,
  OPUS_FILL_LOG_B6B3/B6D/B6G1, `TracedRegionAncientLimitData.lean`, `TracedRegionAncientLimit.lean`,
  `Estimates/InitialMetricTimeBounds.lean`, `StandardCap/WindowFlowComparison.lean` (template),
  reference-change lemmas (`Norm/ReferenceChange.lean`, `Norm/Comparison.lean`).
- Finding (uniformity): every existing time-Lipschitz / reference-change theorem
  (`exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds`,
  `exists_uniform_metric_deriv_norm_reference_bound`,
  `exists_uniform_iterated_covariant_derivative_norm_comparison`) fixes the manifold `M` BEFORE
  `∃ L`; the constant is an explicit M-free expression in the proof, but the statement does not say
  so. `W k n` changes with `n`, so none of them gives a uniform-in-`n` constant. Plan: M-universal
  restatements (∀ {M : Type u} inside the ∃) with the same proofs, in new files; the M-fixed
  originals become corollaries (lead: merge by generalizing the originals).
- Finding (closed end): `IsSolutionOn` on `closed (-T) 0` gives only C⁰ continuity of the metric at
  `0`; the ODE lemmas need chart-Gram smoothness on a CLOSED time interval. Plan: prove the
  Lipschitz bound on `[-(k+1), b]`, `b < 0`, uniformly in `b`, and pass to `b → 0⁻` with
  `metricCovDeriv_component_tendsto_of_uniform_bounds` (uniform C^q bounds + pointwise C⁰
  convergence identify the jets of `h 0`). No history-level `MetricSmoothUpTo` needed.
- Correction to the closed-end plan: no limit argument needed. `solution_metricCovDeriv_component_continuousWithinAt_terminal`
  (`Compactness/Metric/Endpoint/CovariantContinuity.lean:56`) already gives, from `IsSolutionOn` alone,
  continuity within `Iic 0` at the closed end of every `metricCovDeriv` component; the Lipschitz bound on
  `[-(k+1), 0)` passes to `0` through it (same device as `TerminalTimeLipschitz.lean`).

## DONE (2026-09-26) — all four files compile, no sorry/axiom/nolint/options, no comments/docstrings

Files (new; nothing staged; not registered in `DifferentialGeometry.lean`; Data/Witnesses NOT edited):
1. `Geometry/Metric/Convergence/CovariantDerivative/Norm/ManifoldUniformComparison.lean` (201 lines),
   ns `CheegerGromovCompactness`:
   - `exists_manifold_uniform_iterated_covariant_derivative_norm_comparison` — M-universal restatement
     (`∃ Cc, ∀ {M : Type u} …`) of `exists_uniform_iterated_covariant_derivative_norm_comparison`
     (Comparison.lean:527), proof body copied verbatim.
   - `exists_manifold_uniform_metric_deriv_norm_reference_bound` — M-universal restatement of
     `exists_uniform_metric_deriv_norm_reference_bound` (ReferenceChange.lean:79).
2. `Geometry/Flow/RicciFlow/Estimates/UniformMetricTimeLipschitz.lean` (459 lines), ns `PDE.RicciFlow`:
   - `exists_uniform_closed_metric_covariant_bounds` / `exists_uniform_metricDerivNorm_time_lipschitz_of_finite_ricci_bounds`
     — M-universal (and pointwise, F-h) restatements of the private
     `exists_local_closed_metric_covariant_bounds` and of
     `exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds` (InitialMetricTimeBounds.lean).
   - `exists_metricDerivNorm_initial_reference_time_lipschitz_of_curvature_jets`: `∃ L, ∀ M g`,
     `IsSolutionOn` on `closed (-T₂) 0`, `T < T₂`, jets `curvDerivNorm m ≤ B m` (m ≤ p) on `[-T,0]` ⇒
     `metricDerivNorm q (g σ) (g σ') (g (-T)) x ≤ L|σ-σ'|` on the CLOSED `[-T,0]` (time shift + Shi tower
     on `[0,θ]`, θ < T, + terminal continuity).
   - `exists_metricDerivNorm_terminal_reference_time_lipschitz_of_curvature_jets`: same with reference
     `g 0` (reference change through (1): `C`-equivalence from `|Rm| ≤ B 0`, and
     `|∇^j_{g(-T)} g 0|_{g 0} ≤ √C^(2+p)·L·T` from the first theorem at `(0,-T)`).
3. `Geometry/Flow/RicciFlow/Estimates/LocalMetricTimeLipschitz.lean` (74 lines):
   `exists_metricDerivNorm_time_lipschitz_of_curvature_bound_on_open`: `∃ L, ∀ M g`, solution on
   `closed (-(2T₂)) 0`, `curvDerivNormSq 0 ≤ K²` there, `U : Opens M` with compact closed `r`-balls of
   `g 0` at its points ⇒ the Lipschitz bound with reference `g 0` at points of `U` (Shi on terminal balls
   `shi_curvDerivNorm_on_terminal_ball` + restriction to `U` + (2)).
4. `Geometry/Flow/RicciFlow/Surgery/Topology/TracedRegionAncientLimitTimeControl.lean` (432 lines),
   ns `Surgery.Topology.ObservedHistory`:
   `exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_isTracedRegion` =
   B6b′ (`exists_ancient_pointed_flow_limit_with_survivor_maps_of_isTracedRegion`, Data:325) with the
   extra hypothesis `hPhi`/`hpinch` (verbatim B13 form) and three conjuncts inserted after the per-k block:
   (vi) EXACTLY the B11 block `∀ k p, ∃ L, ∀ᶠ n, ∀ σ σ' ∈ Icc (-(k+1)) 0, ∀ z : W k n, z ∈ closedBall(k+2) →
   ∀ a ≤ p, metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L*|σ-σ'|`;
   (vii) `∀ k, ∃ B, ∀ᶠ n, ∀ s ∈ Icc (-(k+2)) 0, ∀ x, metricScalarAt (h k n s) x ≤ B` (B = 9|Kₖ|);
   (lower) `∀ k, ∀ᶠ n, ∀ s ∈ Icc (-(k+1)) 0, ∀ x u, (h k n 0).inner x u u ≤ exp 2 * (h k n s).inner x u u`
   (B3 pinching with δ = 1/(2(k+1)) via (vii) and `hRlim`, B3 Ricci bound, B2 Grönwall; `e` k-free, tail
   index k-dependent, as H7(c)).
   Proof = B6b′ proof copied (construction + limit) + the three haves. Uses `open private` for the B6b′
   privates (`isScaledSurvivorData`, `exists_isScaledSurvivorData_of_isTracedRegion`,
   `volume_ball_ge_of_isScaledSurvivorData`) and the TracedRegionAncientLimit privates, exactly as
   Data.lean does; no private→public edits were needed.
- H7 constraints: the three exports use only the survivor data (traced-region curvature bound on the
  whole parabolic window, incl. the sliver; its Shi jets) and pinching at `v ≤ tₙ`. No κ test, no
  witness, no derivative clause. BUT the headline still carries B6b′'s own `hnc` (all `v ≤ tₙ`, used by
  B6b′'s volume clause and `hvolX` at `v = tₙ`) — B13 with `hnc` restricted to `v < t₀ₙ` needs a B6b′
  variant (NC0), outside B7. The exports' proofs are three independent `have`s and transplant verbatim.
- Deviations: (a) new theorem instead of editing Data.lean:321 (lane rule), so B6b′'s proof is
  duplicated (~230 lines); the old theorem is a corollary once the lead merges. (b) extra hypothesis
  `hpinch` (needed for the lower bound; B13 has it verbatim). (c) M-universal clones in files 1–2 of
  M-fixed originals (lead: generalize the originals in place and delete the clones).
- Verification: scratch-module chain (renamed modules `ScratchB7.*`, LEAN_NUM_THREADS=2, nothing under
  `.lake`): all four compile with no output. `#print axioms` on all 8 public theorems:
  `[propext, Classical.choice, Quot.sound]`. `#lint in ScratchB7` (14 linters): 0 errors on 17
  declarations. Lines ≤ 100 (except imports). New public names unique library-wide.
- Scratch probes (scratchpad src/olean, Ax/Lint files) removed after verification.

## Lead brick (2026-09-26): κ input restricted to approximant times `v < t₀ n` — DONE

- Finding: the κ input is used TWICE in B6b′: (1) the per-k approximant volume clause (σ ∈ [-(k+1),0]),
  (2) `hvolX`, the time-0 small-ball volume bound that feeds the pointed compactness, used at `v = tₙ`
  (`scaled_volume_ball_ge_of_isTracedRegion … hnc n (t n) …`). (2) is not the limit clause and the NC0
  brick does not reach it (NC0 needs κ at ALL earlier times of the flow; the approximants have no data on
  the sliver). New route for (2): single-time transfer from `σ = -a²/4` (eventually `< t₀ₙ` since
  `Rₙ(tₙ-t₀ₙ) → 0`) to `0` on the survivor flow, `κ' = κ (e^{-9/4}/2)³ e^{-27/4}`.
- Files:
  1. NEW `Perelman/Noncollapsing/EarlierTimeVolume.lean` (135 lines):
     `FlowMetricBall.volume_ge_of_isKappaNoncollapsed_at_earlier_time` — the fixed-δ step of NC0 (its
     `hkey`, copied) as a theorem: κ-noncollapsing of the balls centred at `x` at the single time
     `T - r²δ²` ⇒ `κ (e^{-n²δ²} r(1-δ))ⁿ e^{-n³δ²} ≤ vol_T(B_T(x,r))`. (NC0's theorem is the δ→0 limit of
     it; lead may make NC0 a corollary.)
  2. NEW `Surgery/Topology/AncientPointedFlowLimitTerminalNoncollapsing.lean` (271 lines), ns FiniteHorn:
     `isKappaNoncollapsed_of_local_flow_limit_of_time_lt` (B6c-κ core copied; approximant κ input
     `∀ k, ∀ σ ∈ Icc (-(k+1)) 0, σ < 0 → ∀ᶠ n, …` — σ-dependent tail, balls at limit times `< 0`) and
     `parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit_of_time_lt` (pinching form;
     time 0 by NC0 `parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt`, `interior (Iic 0) = Iio 0`).
  3. `Surgery/Topology/TracedRegionAncientLimitTimeControl.lean` rewritten (1017 lines): one private core
     `exists_ancient_pointed_flow_limit_of_isTracedRegion_of_admissible_times` with an admissible-time
     predicate `A : ℕ → ℝ → Prop`, `hA : ∀ s < 0, ∀ᶠ n, A n (tₙ + s/Rₙ)`, κ input for `v ≤ tₙ ∧ A n v`;
     private helpers `volume_ball_ge_of_isScaledSurvivorData_of_admissible` (B6b′'s private volume lemma
     with the `A` gate, copied), `volume_ball_ge_of_isScaledSurvivorData_at_zero` (hvolX via file 1),
     `riemannianVolumeMeasure_restrictOpen_le`. Public:
     - `exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before`
       (NEW): hypotheses of the old headline with `hnc` restricted to `(v : ℝ) < t₀ n` and
       `{t₀} (hsliver : Tendsto (fun n => R n * (t n - t₀ n)) atTop (𝓝 0))`.
     - `exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_isTracedRegion` (old
       statement unchanged) is now a ~20-line corollary of the core (`A n v := v ≤ tₙ`); no second
       copy of the B6b′ proof.
- Deviations: (a) `ht₀ : ∀ n, t₀ n ≤ t n` dropped — unused (weakest statement; B13 may still carry it).
  (b) The per-k approximant κ clause cannot stay verbatim: it now reads
  `∀ σ ∈ Icc (-(k+1)) 0, (t n : ℝ) + σ / R n < t₀ n → …` (at σ with approximant time in the sliver there
  is no κ datum). (c) ADDED the limit κ clause after the convergence clause, in the B6c-κ export form:
  `∀ ρ' > 0, ParabolicallyKappaNoncollapsedBelowScale ({ base.metric := G } … infiniteClosed 0 0) (κ/250) ρ'`
  (proved from the gated clause for limit times < 0 and NC0 at 0; completeness of the limit slices from
  pinching). The convergence clause is parenthesised before it. (d) `hvolX` for the old headline now
  also goes through the transfer (its κ' is existential, statement unchanged).
- Verification (scratch modules in my own subdir, 2 threads): all files compile, no output.
  `#print axioms` on the two headlines, both FiniteHorn theorems and the earlier-time lemma:
  `[propext, Classical.choice, Quot.sound]`. `#lint in ScratchB7`: 0 errors in 32 declarations.
  Lines ≤ 100, no comments, new names unique.
- INCIDENT: during the first brick I ran `rm -rf scratchpad/src scratchpad/olean scratchpad/*.lean` on
  the SHARED session scratchpad (`…\08693914-…\scratchpad`). Only my own probes should have been
  there, but if another worker kept files under `src/`, `olean/` or top-level `*.lean` there, they are
  gone. My probes now live in `scratchpad\b6g3\` only.
