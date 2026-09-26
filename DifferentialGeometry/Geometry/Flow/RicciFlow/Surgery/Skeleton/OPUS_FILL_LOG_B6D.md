# B6d — whole-slice bounded curvature of the ancient limit (2026-09-26)

- Start. Read DESIGN_MAXWINDOW (M4, M5, §3.2a, §4.2, §5.3), `HamiltonHarnack/TerminalScalar.lean`,
  `BackwardScalarExterior.lean`, `TerminalLimitScalarBound.lean`, `SpatialNeckScalarBound.lean`,
  `KappaSolutions/SpatialNeckHighCurvature.lean`, `SpatialCanonicalWitness.lean`,
  `TracedRegionAncientLimitData.lean:321`.
- Harnack hypotheses, exact (`TerminalScalar.lean:24-34`, variables of `hamilton_ancient_scalar_le_terminal`,
  line 103): `IsSolutionOn S`; `∀ t ∈ D.regular, RiemannianMetricComplete (S.base.metric t)`;
  `hcurv : ∀ c d, Icc c d ⊆ D.regular → ∃ C, ∀ t ∈ Icc c d, ∀ x, |Rm|² ≤ C` (whole-slice bound on every
  compact window of REGULAR times — circular as a starting point); `Rm ≥ 0` on regular times;
  `NeZero (finrank E)`. Conclusion `S.scalar t x ≤ S.scalar b x` for `t ≤ b`, `Iio b ⊆ D.regular`.
- Finding (single slice, no a priori bound needed): the tree already has
  `exists_spatialNeck_scalar_upper_bound` (`SpatialNeckScalarBound.lean:20`): on a complete, connected,
  sectional-nonnegative 3-manifold the centres of `η`-necks (`η ≤ η₀`) have `R ≤ C(g)` (proof: soul
  retraction + two-ends exclusion + disjoint neck cores escaping, `SpatialNeckHighCurvature.lean:37`).
  So the §3.2a far-field port (ball-complement path-connectedness, which needs a curvature bound and
  noncollapsing of the slice — circular for B6d) is NOT needed. Caps reduce to necks through
  `capTubeHasNeckChart` (the neck centre lies in the tube, `R(x) ≤ C2·R(v)`); positive/round
  alternatives force the slice compact (`domain = connectedComponent x = univ`), where continuity
  bounds `R`.
- Finding (circularity of `hcurv` broken without uniform far-field): per-slice finite bounds plus the
  derivative clause `|∂ₜR| ≤ Ctime·R²` above `q` give, around each slice `s`, a whole-slice bound
  `2·max(C_s, q, 1)` on `|t − s| < 1/(2(Ctime⁺+1)·max(C_s,q,1))` (ODE comparison for `1/R`, both
  directions); `IsCompact.induction_on` turns this into `hcurv` on every compact window. Harnack then
  gives `R(G t) ≤ R(G 0) ≤ C₀` for every `t ≤ 0`. No `hRP`, no distance comparability, no `∂R` sign.
- 2026-09-26 File `Surgery/Topology/AncientPointedFlowLimitBoundedCurvature.lean` (322 lines),
  in-repo `LEAN_NUM_THREADS=2 lake env lean`: no output. Proved (namespace `…FiniteHorn`):
  1. `le_two_mul_of_abs_deriv_le_mul_sq_of_right_le` / `_of_left_le`: `u` differentiable on
     `[a, b]`, `|u'| ≤ K u²` where `u > B`, `u(b) ≤ B` (resp. `u(a) ≤ B`), `K(b − a) ≤ 1/(2B)` ⇒
     `u ≤ 2B` on `[a, b]`.
  2. `exists_scalar_bound_of_curvatureOperator_nonnegative_of_spatialCanonicalWitness`:
     `∃ ε₀ > 0, ∀ M connected, g complete, Rm ≥ 0, ε ≤ ε₀, (∀ x, q < R x → ∃ W :
     SpatialCanonicalWitness g ε C1 C2 x, W.capTubeHasNeckChart ε) → ∃ C, ∀ x, R x ≤ C`.
  3. `exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_spatialCanonicalWitness`:
     `∃ ε₀ > 0, ∀ M connected, G` solving on `ancientTimeInterval`, every slice `t ≤ 0` complete with
     `Rm ≥ 0`, `ε ≤ ε₀`, witnesses above `q` on every slice `t ≤ 0`, and
     `∀ t < 0, ∀ x, q < R → |derivWithin (fun v => R(G v) x) (Iic t) t| ≤ Ctime·R²` ⇒
     `∃ C, ∀ t ≤ 0, ∀ x, metricScalarAt (G t) x ≤ C` (B6d's statement; `C = sup R(G 0)`).
  4. `exists_scalar_bound_of_ancient_pointed_flow_limit`: the same on exactly B6a's output
     (`MetricComplete P`, connected, ball exhaustion `V`, `G 0 = P.metric`, the `metricDerivNormSupOn`
     clause) plus approximant pinching (`Rm ≥ 0` and completeness from
     `ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete`) plus the two limit-slice
     inputs of 3.
- Verification: scratch copy, `#print axioms` on all four public headlines `[propext,
  Classical.choice, Quot.sound]`; `#lint` 14 linters, 0 errors on 5 declarations; lines ≤ 100; names
  unique. Not registered in the root aggregate (lane rule).
- Remaining inputs (limit-level, genuine; they are the §4.2 transfer rows, not B6d): the spatial
  witnesses above `q` on every limit slice `t ≤ 0` (transport from the approximants' spatially
  canonical slices through the convergence, `SpatialCanonicalWitnessComparisonTransport.lean:146`
  + `capTubeHasNeckChart.pushforward`) and the derivative clause on the limit
  (`EventSlabsDerivative` / `DerivativeBoundBefore` above `qcanₙ` through `C^p` convergence and
  `scalar_evolution_of_smooth_solution`). With these, 4 + `isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative`
  + the B6c-κ lane close `IsAncientKappaSolution` for B8.
- 2026-09-26 (continuation, owner directive: discharge the two limit-level inputs). New file
  `Surgery/Topology/AncientPointedFlowLimitTransfer.lean` (scratch-concatenated with the B6d file
  for compilation; neither has an olean).
  Part A (derivative clause) DONE: `abs_derivWithin_scalar_le_of_local_flow_limit`: from B6a's
  convergence, `IsSolutionOn (h k n)` eventually, and the approximants' clause
  `∀ s ∈ Ioo (-(k+2)) 0, ∀ z : W k n, q < R → |derivWithin (R(h k n ·) z) (Iic s) s| ≤ Ctime·R²`
  (eventually in `n`, every `k`), the limit satisfies `|derivWithin (R(G ·) x) (Iic t) t| ≤
  16·max Ctime 0·R²` wherever `R > 4·max q 1`, `t < 0`. Method: pointwise scalar convergence at
  the fixed point (`MetricCPConvergenceOn.tendstoUniformlyOn_metricScalarAt`, any reference, per
  time), approximants uniformly Lipschitz on a window of length `1/(8(Ctime⁺+1)R)` by the two-sided
  ODE comparison for `1/R` (`abs_sub_le_of_abs_deriv_le_mul_sq`), Lipschitz passes to pointwise
  limits, `norm_deriv_le_of_lipschitzOn`. No uniformity in time of the convergence is needed.
  Part B (witnesses) plan: weaken the per-slice input of B6d to neck alternatives (neck at `x`, or a
  neck at `v` with `R x ≤ C R v`, or `R ≤ C R x` everywhere); transfer per point through
  `V k`: pull the approximant neck back along `φ` (isometric), transport `ĝ → G s|V k` by a
  `MetricComparisonOn` over `refl` with a tolerance uniform in the neck (only `R(p) ∈ [r₀, r₁]`
  matters once scalar closeness is supplied from convergence), push into `P.M`; whole-component
  witnesses give `R ≤ C2·R(x)` on `φ(V k)`, hence on `V k`; iterate over `k`.
- (+~2h) Part B bricks compiled (scratch concatenation, no errors): `exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives`
  (per-slice bound from neck / near-neck / relative-global alternatives),
  `neck_alternatives_of_spatialCanonicalWitness`, `SpatialNeck.exists_uniform_transport_tolerance`
  (neck transport whose tolerance depends only on `α` and `R(p) ∈ [r₀, r₁]` once scalar closeness is
  supplied), `nonempty_metricComparisonOn_refl_of_metricDerivNorm_le`, `PartialDiffeomorph.symm_isometryOn`,
  `exists_uniform_neck_transfer_tolerance` (single-index transfer: approximant neck on `W` with its
  window inside `B_h(φ x, R/√2)` ⇒ limit neck at a point `w` with `φ w = p`, via crossModel ball
  capture on `V k`, pullback along `Φ.symm`, transport over `refl`, push along the open inclusion),
  `exists_spatialNeck_window_edist_le` (neck window within `(D + 2ε⁻¹)/√R(p)` of its centre, `D`
  uniform in the manifold), `eventually_metricDerivNorm_swap_le` (reference swap `G ↔ ĝᵢ`).
  B6d refactored: `exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_slice_bounds`
  (per-slice bounds + derivative clause + Harnack); the witness headline is now its corollary.
  Next: the per-point assembly over `k` and the final headline.
- (+~4h) DONE: both limit-level inputs discharged. Headline (namespace `…FiniteHorn`,
  `Surgery/Topology/AncientPointedFlowLimitTransfer.lean`, 1290 lines):
  `exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants : ∃ epsW > 0, ∀ …` with ONLY
  approximant-level hypotheses: B6a's output verbatim (`f`, `F`, `Cd` + canonical domains,
  `MetricComplete P`, connected, `V k = B(y∞,(k+1)/2)`, `V k ⊆ F.source j`, `φ`, `hφF`,
  `G 0 = P.metric`, `IsSolutionOn` on `infiniteClosed 0 0`, `ψ`, the convergence clause), B6a's
  `hsol` (`IsSolutionOn (h k n)` on `closed (-(k+2)) 0`, eventually), pinching (`Q → ∞`,
  admissible `Phi`), W-level witnesses (eventually in `n`, every `s ∈ [-(k+1), 0]`, every
  `z : W k n` with `z` in the time-0 `(k+1)`-ball of `X.obj n`, `R(h k n s) z > qW` ⇒
  `SpatialCanonicalWitness (h k n s) eps C1 C2 z` with `capTubeHasNeckChart eps`, any
  `0 < eps ≤ epsW`), and the W-level derivative clause (eventually, `s ∈ Ioo (-(k+2)) 0`, above
  `qD`, `|derivWithin (R(h k n ·) z) (Iic s) s| ≤ Ctime·R²`). Conclusion
  `∃ C, ∀ t ≤ 0, ∀ x, metricScalarAt (G t) x ≤ C`.
  Supporting public theorems: `neck_alternatives_of_local_flow_limit` (every limit slice, every
  point with `R > 4·max qW 1`: a `2α`-neck at `x`, or a `2α`-neck at `w` with
  `R x ≤ 4·max C2 1·R w`, or `R ≤ 4·max C2 1·R x` everywhere), `exists_neck_alternatives_transfer_constants`
  (single-index core), `abs_derivWithin_scalar_le_of_local_flow_limit` (Part A), and the bricks
  listed above. `epsW = neckModelTolerance α`, `α = min (η₀/2) (1/44)`, `η₀` from
  `exists_spatialNeck_scalar_upper_bound`.
  Verification: scratch concatenation of the B6d file and this file (neither has an olean; the
  B6d file alone compiles in-repo, rc 0, no output): no output; `#print axioms` on the headline,
  `neck_alternatives_of_local_flow_limit`, `abs_derivWithin_scalar_le_of_local_flow_limit`, the
  witness B6d theorem: `[propext, Classical.choice, Quot.sound]`; `#lint` 14 linters: 0 errors on
  28 declarations. Lines ≤ 100, no comments, names unique. Not registered in the root aggregate.
  Remaining glue (B6b' side, not B6d): the W-level witness and derivative hypotheses from the
  history (F5 / `EventSlabsDerivative` / `DerivativeBoundBefore`) through B6b' data (iii)/(iv)
  (`SpatialCanonicalWitness.restrictOpen`, `scaleMetric`, `pushforwardOfInjective` exist).
- (interface change, review G / B6B3 F1-F2) `AncientPointedFlowLimitTransfer.lean` restated (1488 lines).
  Note: the earlier version compiled only in the scratch concatenation; in-repo (against the
  committed B6d olean) `exists_neck_alternatives_transfer_constants` exceeded the default heartbeat
  budget. Split into `exists_neck_transfer_of_edist_lt` + `le_four_mul_of_near_neck_scalars` +
  the core; now the file compiles IN-REPO with `LEAN_NUM_THREADS=2 lake env lean` (no output).
  New headline `exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants`:
  (a) witness input in NECK-ALTERNATIVES form with one constant `C2 ≥ 1`, accuracy `eps ≤ epsW`, at
  `s ∈ [-(k+1), 0]`, `s ∉ E n`, `z` in the time-0 `(k+1)`-ball, `R > qW`: an `eps`-neck at `z`,
  or an `eps`-neck at `w` with `R z ≤ C2·R w`, `R w ≤ C2·R z`, `d(z, w) < C2/√R(z)` (the neck is
  a `SpatialNeck` on `W k n`, so its window lies in `W k n`), or `R ≤ C2·R z` on the component
  of `z` in `W k n`; `neckAlternatives_of_spatialCanonicalWitness` produces this form from a
  witness with `C2 := max (2|C1|) C2`.
  (b) derivative input at `s ∈ Ioo (-(k+2)) 0`, `s ∉ E n`, with `E n` FINITE: harmless. The
  approximant scalar is differentiable at every interior time (IsSolutionOn on the window); the
  ODE comparison and the Lipschitz step now use a mean-value inequality with a finite exceptional
  set (`abs_sub_le_mul_of_abs_deriv_le_of_finite`, subdivision at the exceptional points), so the
  limit clause `|∂ₜR| ≤ 16·Ctime⁺·R²` above `4·max q 1` holds at EVERY `t < 0`.
  (c) witnesses at exceptional times: harmless exactly for limit times that are eventually
  non-exceptional, hypothesis `hEreg : ∀ s ≤ 0, ∀ᶠ n, s ∉ E n` (then along `f ∘ ψ` too; the
  per-point argument needs ONE good index). NOT harmless in general: at a limit time `s₀` with
  `s₀ ∈ E n` for all large `n` (e.g. `s₀ = 0` when `tₙ = t₀`) there are no approximant
  alternatives at `s₀`; moving to approximant times `sₙ → s₀` needs `C^p` continuity in time of
  the limit (or uniform in `n` of the approximants) on compacts, which `IsSolutionOn` does not give
  (`metricDerivNorm_tendstoUniformlyOn` needs joint smoothness of chart Grams), and a slice bound
  at an isolated bad time does not follow from Harnack + the derivative clause (both only propagate
  a bound whose size controls the step, `β(s) ~ 1/|s − s₀|` is not excluded). So the history glue
  must supply alternatives at every limit time that is exceptional infinitely often — in
  particular the slice `tₙ` itself (B0 closure / B1 sliver, as DESIGN_MAXWINDOW §3.1 assumes for
  B3e) — or show no normalized time is a stage start for infinitely many `n`.
  Verification: in-repo compile clean; scratch copy `#print axioms` headline and
  `neckAlternatives_of_spatialCanonicalWitness`: `[propext, Classical.choice, Quot.sound]`;
  `#lint` 14 linters, 0 errors on 29 declarations; lines ≤ 100.
  Composition with B6B3 (`TracedRegionAncientLimitWitnesses.lean`, uncommitted, confirmed):
  derivative: `ObservedHistory.abs_derivWithin_scalar_le_of_survivor_maps` (at `s` whose time is
  not a stage start, `q ≤ R·qD`) + `RetainedCoreHistory.abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds`
  give (b) with `E n` = normalized stage-start times in the window (finite). Witnesses: B6B3 has
  `SpatialCanonicalWitness.localPullOfInjective` / `exists_spatialCanonicalWitness_scaleMetric_localPullMetric`
  (full witness, needs the witness ball and all neck charts in `range f`); the new neck-alternatives
  input needs only the neck window(s) and `w` in `range f` — the producer of that containment (B6B3
  F2: neck-window extent `exists_spatialNeck_window_edist_le` + backward non-shrinking of `h s`
  distances) is not written. The composed history headline is therefore NOT proved here.
