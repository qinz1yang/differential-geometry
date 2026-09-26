# B6b + B7 — history glue to the ancient pointed limit, and the depth induction (2026-09-26)

- Start. Read AGENTS.md, NAMING §2–6, Skeleton/README, DESIGN_CROSSING, OPUS_FILL_LOG_B6A/B5.
- Read B6a (`AncientPointedFlowLimit.lean`), B5, B2 (`TracedRegion.lean`), B4, Shi template
  (`TracedTerminalCompactness.lean:108`), `HistoryTerminalVolume.lean:407`,
  `isSolutionOn_parabolicClosedWindow` (`Scaling/ClosedWindow.lean:38`), `shi_curvDerivNorm_on_terminal_ball`
  (`Estimates/Shi/Derivatives/TerminalBall.lean:373`), `riemannianVolumeMeasure_ball_ge_scaleMetric_iff`
  (`Geometry/Measure/BallComparison.lean:49`).
- Plan B6b: X.obj n = (stage at tₙ, Rₙ·g(tₙ), yₙ) (compact carriers, so all closed balls compact);
  W k n = B2 survivor ball of normalized radius k+3, depth 2k+4; h k n = `parabolicClosedWindow` of the
  B2 survivor flow; jets by Shi on the window [-(2k+4),0] (B2's bound holds on all of U); overlaps by
  building a `BackwardPointTrace` from B2's maps and `point_unique`; volume tests from the time-t
  noncollapsing on parabolically controlled history balls (`isTracedRegion.mono` gives the control).
- Finding (B7, failure first): see the entry below once analysed.
- (+~1h) B6b file `Surgery/Topology/TracedRegionAncientLimit.lean` compiles (scratch concatenation
  TracedRegion + CompactBalls + AncientPointedFlowLimit + this file, `LEAN_NUM_THREADS=2 lake env lean`,
  0 errors). Headline `ObservedHistory.exists_ancient_pointed_flow_limit_of_isTracedRegion`.
- B7 finding (failure): the depth induction cannot be closed from the listed suppliers. Plain
  iteration of B4 doubles the bound each step (depth steps 1/(4·Ctime·2^i·Q) sum to < 1/(2·Ctime·Q)),
  and "re-anchoring by the limit" adds nothing: an anchor at depth T is already the hypothesis being
  iterated; what is missing is a bound on the partial limit on B̄(A) × (−T∞, 0] uniform as T ↑ T∞
  (the finite-horizon curvature bound of the limit, B6c/F9: completeness of the limit slices + Rm ≥ 0
  + a backward curvature bound, cf. the smooth template
  `exists_uniform_backward_scalar_bound_on_finite_horizon`). Delivered instead the B7 step in B5's
  `hscal` shape: `Surgery/Topology/TracedRegionDepthStep.lean` (compiles, scratch concat with B4).
- DONE (B6b; B7 step only). Verification: scratch concatenations outside the repo (B6b: TracedRegion +
  CompactBalls + AncientPointedFlowLimit + file; B7 step: TracedRegionBackwardStep + file) with
  `set_option linter.mathlibStandardSet true` on the new file, `LEAN_NUM_THREADS=2 lake env lean`:
  0 errors, 0 warnings in the new files; `#lint` (14 linters): only docBlame on B2's three defs
  (excluded linter); `#print axioms` of the three public theorems: propext, Classical.choice,
  Quot.sound. New public names unique library-wide. Lines ≤ 100. Scratch removed. Not registered in
  the root aggregate (their imports TracedRegion / AncientPointedFlowLimit / B4 are not registered).
- B6b headline `ObservedHistory.exists_ancient_pointed_flow_limit_of_isTracedRegion`: inputs `Hₙ`,
  `tₙ`, `yₙ`, `Rₙ > 0`, `Rₙ → ∞`, `htraced : ∀ A T > 0, ∃ K ≥ 0, ∀ᶠ n, isTracedRegion tₙ yₙ (A/√Rₙ)
  (T/Rₙ) (K·Rₙ)` (B5's left branch with K = 8√3(1+φ1+φ0)·Q), and time-tₙ noncollapsing on
  parabolically controlled history balls of radius ≤ ρ (`NoncollapsedBefore κ ρ t₀` with tₙ ≤ t₀ gives
  it pointwise). Output: `X.obj n = (stage at tₙ, Rₙ·g(tₙ), yₙ)`, `W k n`, `h k n` with, eventually in n,
  `W k n` = normalized ball of radius k+3 and the current-slab clause `h k n s = Rₙ·g(tₙ + s/Rₙ)|W` (what
  B8b's F4 transport against `G.flow` uses), plus B6a's full conclusion (complete connected pointed
  limit, compatible exhaustion `V k`, maps `φ`, ancient `G` on `P × (−∞,0]` with `G 0 = g∞`, `C^p`
  convergence on compacts of `V k × [−(k+1), 0]`). Internals: B2 survivor flows on radius k+3, depth
  2k+4, `parabolicClosedWindow`; Shi (`shi_curvDerivNorm_on_terminal_ball`) at radius 1; overlaps by
  a `BackwardPointTrace` built from B2's maps + `point_unique` + `localPullMetric_restrictOpenOfSubset_eq_of_comp_eq`.
