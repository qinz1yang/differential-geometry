# B3b — cone part of bounded curvature at bounded distance (2026-09-26)

- start: reading AGENTS.md, NAMING.md, B3 log, B3a file, DESIGN_CROSSING, suppliers.
- read: B3 log, B3a file, DESIGN_CROSSING, CanonicalNeighborhoodInduction (working tree),
  SpatialCanonicalWitness, Neck/Spatial, ConeTerminalExclusion, ConeExclusion
  (`rescaled_end_cone_exclusion`), NormalizedBoundedCurvature/NormalizedConeExclusion (template),
  TracedTerminalCompactness (:376, :1031), TracedRegion, TracedRegionBackwardStep, EventData
  (`MetricCutCapEvent`, `SmoothCutCapTransition`), RetainedCoreTower (`RetainedCoreEvent`).

## Verdict: B3b is FALSE as stated in OPUS_FILL_LOG_B3.md (no Lean written, lane stopped)

Defect: B3b has no hypothesis giving a backward parabolic neighbourhood near the high-curvature
points of the ball. Route step (2) ("the traces exist by the derivative bounds and the backward
step") fails: a point in a region inserted at an event inside the window has no
`BackwardPointTrace` at all, and nothing constrains the inserted metric. `RetainedCoreEvent` /
`SmoothCutCapTransition` only require `old_metric_eq` on the retained core; the metric on the
`ThreeBall` cap is arbitrary. B3b has no `InCutoffClass`, no records, no standard-cap comparison.
B4 (`TracedRegionBackwardStep`) likewise takes the crossing trace as a hypothesis (`htrace`).

Counterexample. Fix any `ε̄ ∈ (0, 1/11)` (so any `ε̄cone`), `κ = 10⁻³`, `C1s = C2s = 100`,
`Ctime = Cgrad = 10`, and an admissible `phi ≥ max(1, √s)` for large `s`. Take
`α := ε̄²/100` and `A := 3/α`. Given any `Q Λ ≥ 1`:
1. Stage 0 is `S³` carrying a dumbbell: two fat round bulbs (`R < q`) joined by a long neck. Its
   Ricci flow runs on `[0, T]` with `T > Λ`. Every point with `R > q` is an ε̄-neck, the
   curvature operator is nonnegative up to errors `≤ 1 ≤ phi`, `|∂ₜR| ≤ 10R²`,
   `|∇R| ≤ 10R^{3/2}`, and the flow is κ-noncollapsed on controlled balls. The event at `T` cuts
   the neck at a cross-section of radius `r_c` with `R = 1`, keeps one bulb and caps it with a
   ball.
2. The metric on the ball (unconstrained) is rotationally symmetric. It starts as the cylinder
   (smooth match), then narrows along a cone of slope `α` to a pinch of radius `s`. The profile
   is `f = √(s² + α²z²)`, lengthened near `z = 0` so that the radial curvature satisfies
   `α/(ℓs) ≤ phi(2/s²)`. It then widens with slope `α` until `R < q`, and closes with a fat
   low-curvature cap. All scale-invariant derivatives of `f` are `≤ α ≪ ε̄²`, so every point
   with `R > q` is the centre of an ε̄-`SpatialNeck` over `(−1/ε̄, 1/ε̄)` (relative radius
   change `≤ α/ε̄`). `SpatialLocalNeck` data on `[−10, 10]` then gives a
   `SpatialCanonicalWitness` with `C1s = C2s = 100`: scalar ratio `≤ 1 + 20α`,
   `rm_bound`, volume, gradient. Here `capTubeHasNeckChart` is vacuous, since there are no caps.
3. Stage 1 runs Ricci flow on `[T, t]` with `t − T = δ ≪ s²`. By smooth dependence, every slice
   stays scale-invariantly `C^{⌈1/ε̄⌉}`-close to the inserted metric. So
   `SpatiallyCanonicalBefore`, the witnesses at `t`, `DerivativeBoundBefore 10 q`, the gradient
   bound and `PhiAlmostNonnegative phi` all hold. `EventSlabsSpatiallyCanonical`,
   `EventSlabsDerivative` and `EventSlabsPinched` hold by 1. `q := 1/(2Λ)`, so `Λq < R(y,t) = 1`
   for `y` next to the cut. The window `[t − Λ, t] ⊆ [0, t]`.
4. `NoncollapsedBefore κ ρ t` for every `ρ`: a controlled ball `B(p, r)` needs
   `|Rm| ≤ r⁻²` along traces over time `r²`. In the inserted region the traces stop at `T`, so
   `r² ≤ δ` and `r ≤ c·(local radius)`. That is a neck-scale ball, with volume `≥ κr³`. The
   dumbbell is as in 1.
5. The pinch `z` has `d_t(y, z) ≈ √2/α < A` (normalized), and `R(z,t) ≈ 2/s²`. As `s → 0`,
   `R(z,t)/R(y,t) → ∞`, so no `Q` works.
   The cone exclusion does not apply because normalized backward room at cone points is
   `δ·R ≪ 1` (the flow is younger than every cone scale). This is exactly the input B3b lacks.

Two repairs:
- (i) no event in the window: add `H.time (H.activeStage t) ≤ t − Λ/R(y,t)`. The ball then
  lives on one slab. Every point has a trace over the whole window, and step 2 follows from B4
  on a single stage. The initial metric of the slab is then at least `Λ/R(y)` older than `t`,
  which gives normalized room `≥ Λ·R(x)/R(y)` at escape points.
- (ii) the Crossing form: add B5's record hypotheses (`records`, `hbirth`, `ha₀`,
  `modelAccuracy ≤ ζ₀`, `Dstar ≤ modelRadius`) and `¬ H.CapWindowPoint records _ y t Dcap θcap`,
  with `∃ Q Λ Dcap θcap` after `A`. Inside the contradiction, B5 runs at the base on the balls
  `B(y, ρ/√R)` for `ρ < ρ̄`, at depth `θ/R(y)` with `θ = 1/(8·Ctime·Q(ρ))` (so `hQ` comes from
  the derivative bound). This yields the traces the cone step needs at the points `xₙ`, which
  lie at distance `< ρ̄`.
  (i) is the smaller brick. (ii) is what Crossing consumes when events fall in the window
  (F3/F5).

## Suppliers checked for the corrected brick (usable as-is)
- `rescaled_end_cone_exclusion` (`Compactness/ConeExclusion.lean:172`): the generic cone
  exclusion. Inputs: a `PuncturedConeApproximation` at the missing point, `xₙ → q0` with
  `R·d² ∈ [c, B]`, and a local backward limit flow at `xₙ` with `SecLower 0`. It is not tied
  to `NormalizedSequence`, so it is the right endpoint instead of calling
  `solution_cone_terminal_exclusion` directly.
- The escape radius: `exists_terminal_scalar_escape_radius_of_derivative_bounds` (used at
  `TracedTerminalCompactness.lean:1031`). It works for any slice through `ClosedSlab` +
  `endpointTerminalLimitMetric`.
- The pointed limit given buffered traces:
  `exists_normalized_terminal_pointed_convergence_of_backward_traces_and_volume_tests` (`:265`).

No Lean file created; nothing compiled; no axioms to report.
- 09:34 wrote Topology/BoundedCurvatureAtDistanceLimit.lean (escape radius + incomplete pointed limit under the one-slab window); first compile blocked by a missing olean (StandardCap/InitialTipCurvature, build in progress); retrying every 10 min.
- 09:39 progress: file restructured (own volume lemma with scale-invariant noncollapsing radius σᵢ√Qᵢ ≥ σ₀, since TerminalNoncollapsedBefore only gives ρ ≥ Λ/√R; glue lemma from TerminalNoncollapsedBefore). Waiting on oleans (a build is rebuilding Perelman/CanonicalNeighborhood); compile scheduled.
- 09:59 compiles clean (after: inline G in the htested let — a let-fvar there gave 'unknown free variable'; dsimp at the supplier output before obtain — whnf timeout). Axioms propext/choice/Quot.sound; #lint 14 linters ok; renamed headline of the file to fit 100 cols.

## Repair (i): delivered up to step 3; steps 4-5 stated as B3c (2026-09-26)

File `Surgery/Topology/BoundedCurvatureAtDistanceLimit.lean` (409 lines, no sorry, not registered).
Namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`.

- `RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_final_slab_window`
  (steps 1–3). Input: sequences `H i` (retained-core histories) and closed slabs
  `A i : ClosedSlab (time last) (time i)`, with `hinit` and `horizon < time i`.
  - Bounds at threshold `q i > 0`: event-slab `|∂ₜR| ≤ Ctime R²`, and on the final slab
    `|∂ₜR| ≤ Ctime R²` and `|∇R| ≤ Cgrad R^{3/2}`.
  - Base point `x i` with `1 ≤ Qᵢ := R(x i, time i)` and `q i ≤ Qᵢ`.
  - One-slab window: `time last ≤ time i − θ₀/Qᵢ`.
  - Failure `∃ R₀, ¬ bounded R/Q on normalized balls of radius R₀`.
  - `EventSlabsPinched`-shaped pinching and final-slab pinching.
  - Scale-invariant noncollapsing: tests at radii `b ≤ σ i` with `σ₀ ≤ σ i·√Qᵢ`.
  Output: the escape radius `ρ̄ > 0`, subsequences `ind`, `f`, and the incomplete pointed limit
  `P` of the normalized slices. `P` has `R(base) = 1`, lies inside `B(ρ̄)`, has compact closed
  balls below `ρ̄`, and comes with capture of `B(rₙ)`, `rₙ → ρ̄`, and `C⁰` metric closeness.
  Escape points `zₙ` satisfy `dₙ → ρ̄` and `R(zₙ)/Qₙ → ∞`. The output shape is that of
  `…at_scalar_escape_of_scalar_derivative_contact` (`TracedTerminalCompactness.lean:1160`), with
  the contact and cap-record hypotheses replaced by the window: traces are
  `BackwardPointTrace.singleton`.
  Suppliers: `exists_terminal_scalar_escape_radius_of_derivative_bounds`
  (`TerminalCurvatureEscape.lean:166`) and
  `ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces`
  (`TracedTerminalCompactness.lean:168`). The volume lemma is a scale-invariant copy of the
  private `:531` lemma (σ per index), built on
  `exists_uniform_parabolically_controlled_incoming_terminal_ball_radius`
  (`ParabolicTerminalBallFlow.lean:561`) and
  `normalized_terminal_volume_ball_ge_of_tested_incomingFootprint_flow_ball`
  (`HistoryTerminalVolume.lean:407`). This copy was needed because the `:265`/`:671` suppliers
  take one fixed σ, whereas `NoncollapsedBefore κ ρ t` with `ρ√R ≥ Λ` only gives `ρ` scaled with
  `R^{-1/2}`.
- `RetainedCoreHistory.noncollapsedBefore_closedPrefix_of_terminalNoncollapsedBefore` is the glue
  lemma. For an interior slice `t` of the terminal slab `G`, `TerminalNoncollapsedBefore … G … t₀`
  gives the tests for `S := G.closedPrefix t` in exactly the form the main theorem takes. The
  double closed prefix of `G` is definitionally equal to `G.closedPrefix`.
- Compile: `LEAN_NUM_THREADS=2 lake env lean <file>` gives no output; with
  `-Dweak.linter.mathlibStandardSet=true` also clean. On a scratch copy: both public theorems
  depend on `[propext, Classical.choice, Quot.sound]`; `#lint`: 14 linters, 0 errors.

### B3c (not in the tree; > 500 lines; not attempted)

The cone exclusion at the missing point, stated on L1's input (no sorry, no packaged hypothesis).
Fix `κ > 0`, `C1s C2s ≥ 1`, `Ctime Cgrad`, and admissible `phi`. Then `∃ εcone > 0` such that for
every `ε ∈ (0, εcone]` there is NO data meeting all of the following:
- L1's hypotheses with this `phi`, `κ` and `(σ₀, σ)`;
- (a) `Tendsto (fun i => (time i − time last)·Qᵢ) atTop atTop`;
- (b) `Tendsto (fun i => q i / Qᵢ) atTop (𝓝 0)`;
- (c) `Tendsto (fun i => σ i·√Qᵢ) atTop atTop`;
- (d) for all `i`, all `τ ∈ Ioc (time last) (time i)` and all `y`: if `q i < (A i).flow.scalar τ y`
  then `∃ W : SpatialCanonicalWitness ((A i).flow.base.metric τ) ε C1s C2s y`,
  with `W.capTubeHasNeckChart ε`;
- (e) L1's failure hypothesis.
Route: L1, then `SecLower 0` on `P` (the rescaled pinching tends to 0 because `Qᵢ → ∞`). Then
move the witnesses of (d) to necks near the missing point and build the missing endpoint with a
`PuncturedConeApproximation`; these are ports of `NormalizedEscapeLimit` / `NormalizedLimitNecks`
/ `NormalizedNeckSequence` with spatial witnesses in place of `OrientedWitness`. Next take local
backward limits at the neck points `xₙ`: L1 again at base `xₙ`, whose window is automatic by (a)
since `R(xₙ) ≥ R(y)`, plus `exists_compatible_historical_solution_limits_of_pointed_convergence`
(`TracedTerminalCompactness.lean:1959`) and the rescaled pinching. Finish with
`rescaled_end_cone_exclusion` (`Compactness/ConeExclusion.lean:172`). Estimate 3–5k lines:
the template chain is about 3.5k lines on `NormalizedSequence`.

### Headline B3b(i) (terminal-slab form) = contradiction + L1 + B3c

```
∃ εcone > 0, ∀ ε ∈ (0, εcone], ∀ A > 0, ∃ Q Λ, 1 ≤ Q ∧ 1 ≤ Λ ∧
∀ P₀ (H : RetainedCoreHistory P₀) (hend : H.time last = H.horizon) {t}
  (S : ClosedSlab (H.time last) t) (hS : initial) y q ρ,
  1 ≤ q → Λ*q < S.flow.scalar t y → H.time last ≤ t − Λ / S.flow.scalar t y →
  (∀ τ ∈ Ioc (H.time last) t, ∀ x, q < R(x,τ) → ∃ W : SpatialCanonicalWitness … ε C1s C2s x,
    W.capTubeHasNeckChart ε) →
  H.EventSlabsDerivative Ctime q last → S'.DerivativeBoundBefore Ctime q t →
  S'.GradientBoundBefore Cgrad q t → H.EventSlabsPinched phi →
  PhiAlmostNonnegative S'.flow (Ico (H.time last) t) phi →
  H.TerminalNoncollapsedBefore hend S' hS κ ρ t → Λ ≤ ρ * √R(y,t) →
  ∀ z ∈ B_t(y, A/√R(y,t)), R(z,t) ≤ Q * R(y,t)          -- S' := S.restrictIncoming …
```
- It takes `1 ≤ q` in place of `0 ≤ q`: the suppliers need `0 < q ≤ Q` and `1 ≤ Q`, and there is
  no history rescaling API. Crossing has `qcan ≥ 1`.
- Contradiction with `Q = Λ = n` gives L1's data: `σ i = ρᵢ`, `σ₀ = 1`,
  (a)–(c) from `Λₙ → ∞`, and (e) from the bad points. B3c then closes it.
- Interior slices of the terminal slab `G` use `S := G.closedPrefix t` and the glue lemma.
- Slices of earlier event slabs need a history-prefix restriction of `RetainedCoreHistory` (not in
  the tree for retained-core histories; `ObservedHistory.restrict` exists). They are not covered
  here.
