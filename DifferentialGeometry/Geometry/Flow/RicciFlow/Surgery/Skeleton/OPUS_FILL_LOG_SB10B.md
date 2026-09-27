# SB10B — brick B10b, terminal-to-slice transfer for the horn separation (2026-09-26)

- start: read AGENTS, NAMING, Skeleton README, SB10 (three missing items), B10 file, DESIGN_S_FACTORY B9/B12.
- consumer shape (DESIGN_S_FACTORY §3 accuracy chain, step 3): "H gives `StrongNeck G.flow εs x τ` for all
  `τ` near `s`"; B12 row: "Assembly: H at `τₙ → s`, then `TerminalNeckNormalization:434`".

## Outcome: DONE, sorry-free. File `Surgery/Topology/HornSeparationSliceTransfer.lean` (375 lines), not registered.

### Public statements
- (2) `IncomingSlab.TerminalLimitMetric.eventually_riemannianBallOf_subset_image_closedBall`:
  `IsCompact (closedBall_L x r)`, `0 < r` ⇒ `∀ᶠ t in 𝓝[<] s, ball_t(x, 16r/17) ⊆ val '' closedBall_L(x, r)`.
  (compact quad bound `TerminalMetricCompactComparison:50` + `ball_subset_image_closedBall_of_metric_lower`
  `Comparison/BallCapture:25` with the open-subtype partial diffeomorph.) Also gives the (3) lower bound.
- (1) `IncomingSlab.TerminalLimitMetric.eventually_exists_spatialNeck_of_normalizedNeck`:
  `N : NormalizedNeck L.metric δ k`, `δ ≤ neckModelTolerance α / 2`, `⌈(neckModelTolerance α / 2)⁻¹⌉₊ ≤ k`,
  `0 < α`, `2α < 1/11` ⇒ `∀ᶠ t in 𝓝[<] s, ∃ nk : SpatialNeck g(t) (2α) N.center, ∀ z, nk.map z = N.chart z`
  (SAME map). Route: `L.converges` on a compact neck window → `MapMetricApproximationOn.ofMetricDerivNorm`
  → `MetricComparisonOn.ofMapMetricApproximation` → `.staticRescale` (R_L vs R_t) →
  `SpatialNeck.exists_transport_of_local_comparisons` (`SpatialNeckLocalTransport:77`).
- terminal sides `TerminalCorePresentation.exists_deep_horn_centralSphere_side_points`: ∃ eta, same N-prefix
  as B10, `0 < r`, compact `closedBall_L(center, r)`, frontier distance `> r` ⇒ U V open disjoint,
  `(N.chart '' {z.2 = 0})ᶜ ⊆ U ∪ V`, `y ∈ U`, `z ∈ V` at L-distance exactly `r` (B10's private
  `horn_sides_of_complementPair` via `open private`).
- headline `TerminalCorePresentation.exists_strongNeck_threshold_of_horn_point_at_slice`: slab binders
  (delta<1/11, kappa, rho, Phi) ⇒ ∃ A Q₀ θ eta > 0, ∀ P (ε ≤ eta) c e, ∃ Q, ∀ N (B10 prefix) {K},
  frontier distance `> 2A/√R_L`, `R_L ≤ K` on `ball_L(center, 5A/√R_L)` ⇒
  `∀ᶠ τ in 𝓝[<] D.endTime, Q₀ ≤ R(x,τ) → a ≤ τ − θ/R(x,τ) → pinching on [τ−θ/R, τ] → κ-clause on the
  window → Nonempty (StrongNeck D.slab.flow delta x τ)`. Slice neck at α = 1/504 (2α = 1/252); U_τ = val''U;
  radii: ball 19A/4 (compact since < 5A), exclusion ball 7A/4, upper 3A; `|R_τ − R_L| < R_L/10`.

## Checks
- B10 has no olean; `LEAN_PATH` prepending fails (Lean picks the first root holding `DifferentialGeometry`).
  Compiled a scratch concatenation (B10 body + this file, `open private` line dropped) outside the repo:
  `LEAN_NUM_THREADS=2 lake env lean` clean, also with `-Dweak.linter.mathlibStandardSet=true`.
  `open private … from <module>` mechanism checked separately on `IncomingSpatialNeck` (clean).
- Axioms (scratch): all four public theorems [propext, Classical.choice, Quot.sound]. `#lint`: 0 errors in
  17 declarations, 14 linters. Lines ≤ 100 chars. No git writes, no lake build, not in the root aggregate.
