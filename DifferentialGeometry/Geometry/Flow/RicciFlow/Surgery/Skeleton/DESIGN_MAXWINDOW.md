# Design: the maximal-window argument for the Crossing core, 2026-09-26

Read-only design on `codex/pc-target-c-psf` @ a161fc07e. Paths below are relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/`. Sources: review digest F (items 1–4), DESIGN_CROSSING,
logs B3C/B3D/B4/B5/B6A/B6B/B6B2/B6C/B7/B8, the delivered `Surgery/Topology/` files, and the smooth
templates `Perelman/CanonicalNeighborhood/BackwardScalarBound.lean:22`,
`BackwardScalarExterior.lean:89`, `BackwardFiniteHorizon.lean:23`, `BackwardContinuation.lean:532`,
`HamiltonHarnack/TerminalScalar.lean:64,103`, and `Estimates/Distance/TerminalScalar.lean:173`.

## 0. Failures first

**M1 (blocker): B3d cannot serve the base slice or the slices at depth.** The only bounded-curvature-at-distance
headline, `exists_scalar_bound_at_distance_of_bounded_threshold`
(`Surgery/Topology/BoundedCurvatureAtDistanceBoundedThreshold.lean:901`), applies only on the
**final closed slab**, and it requires the window `H.time last ≤ t − Λ/R(y,t)` with `Λ ≥ 1`. Its
first-level limit (`…Limit.lean:182`, hypothesis `hwindow`) needs this event-free backward window.
- Crossing bad points are **young**: `R·(t − a) < θ`. Along the sequence `Rₙ(tₙ − aₙ)` may tend to 0,
  so the window fails at the base slice whenever `θ ≤ Λ`. For the same reason B8's old-base witness
  is irrelevant here.
- The slices used at depth are `tₙ + s/Rₙ`, `s ∈ (−T*, 0]`. They sit in arbitrary slabs, just after
  events, and events can be dense in normalized time (digest C Q5). The tree has no
  `RetainedCoreHistory` prefix operation: only `ObservedHistory.restrict`
  (`Surgery/Topology/HistoryRestriction.lean:232`) and `extendHorizon`.

`Λ ≤ R(y,t)` itself is not a problem: `Rₙ > qcanₙ ≥ n`, and every rebased point has
`R ≥ qsₙ ≥ qcanₙ`. **Required new brick B3e**, bounded curvature at distance on an arbitrary history
slice (§3.1). It replaces the final-slab window by the per-point X2 dichotomy: each point has a small
traced parabolic neighbourhood, or it is a `CapWindowPoint` whose standard-cap geometry supplies the
jets. This dichotomy is needed at two places: the first-level compactness at base scale, and the
second-level end points. Estimate 2.5–5k lines. B3e is used twice: at the base, and for the
recentred propagation `hRP` at depth. The whole route needs it; nothing below removes it.

**M2 (false as briefed): "T* = sup T such that for every A the region is eventually traced" is not
stable under subsequences.** Every limit step (partial limit, bound near the end) passes to a
subsequence. The extension then holds only along that subsequence, with a gain `Δ` that depends on the
limit, so it does not contradict maximality for the original sequence. Fix (§2): take
`T*(σ) := sup {T | DepthExtendable σ T}` over strictly monotone `σ`, and use a diagonal lemma to find
`σ∞` that no further subsequence extends. Generic, 150–300 lines.

**M3 (false as briefed): the base case "T > 0 from B5 + the bounded-depth B7 step + B3d" does not
give one `T₀` for all `A`.** B7's step (`TracedRegionDepthInduction.lean:17`, `2·Ctime·Q·T ≤ 1`) has
depth `≍ 1/(Ctime·Q(A))`, which tends to 0 as `A → ∞`. `DepthExtendable T₀` needs `T₀` independent
of `A`. Fix: prove the **time-zero whole-slice bound** on the time-0 spatial limit first (§3.2). It
gives an `A`-independent `R ≤ 2C₀Rₙ` on every normalized ball, so `T₀ = 1/(4·Ctime·C₀)`. The
reviewer's time-zero bound therefore also carries the base case, not only B6d.

**M4 (the reviewer's sketch is incomplete as an argument).** "Uniform bound near the finite end from
the spatial data" does not follow pointwise: the spatial data give no sign of `∂ₜR`, and at cap cores
there is none. The argument that closes is the **bootstrap** of §4.2:
1. Hamilton's trace Harnack in the tree gives distance comparability
   (`ricciFlow_additive_distance_bound_of_terminal_scalar`, `Estimates/Distance/TerminalScalar.lean:173`).
   Its constant `A_H = (20/3)√(2T*Q₀)√T*` does not depend on the window.
2. The far-field bound (port of `BackwardScalarExterior.lean:89`) and the recentred propagation
   `hRP` (from B3e) then give a bound `C*` that is independent of the window's left end `a`.
3. The limit's derivative bound extends every bounded window backward by `δ = 1/(2·Ctime·C*)`.

This is the smooth template `exists_uniform_backward_scalar_bound_on_finite_horizon` plus the
derivative-bound step.

**M5 (correction to the B6C log: B6d is closable).** `hamilton_ancient_scalar_le_terminal`
(`HamiltonHarnack/TerminalScalar.lean:103`) gives `R(G t) ≤ R(G 0)` for all `t ≤ 0` once each compact
window has a whole-slice bound, which §4.2 supplies. With the time-zero bound this is exactly
`globalScalarBound`. No `hsign` is needed.

**M6 (statement-level, Crossing leaf): B5's `hbirth` cannot be supplied.** B5 needs
`qcan ≤ Cbirth·scale` for every record. The only supplier,
`IsCanonicalCutoffRecordFamily.birth_scale_bounds` (`Surgery/Topology/CapWindowContinuationAssembly.lean:154`),
needs `ρmax² ≤ Cbirth/(4·qcan)`. `CrossingContinuation` quantifies `∃ … δmax ρmax εcap …` **before**
`∀ qcan`; `CapWindowContinuation` quantifies them after it. Proposed fix: move `δmax ρmax εcap` after
`∀ qcan` in `CrossingContinuation`, as in `CapWindowContinuation`. The assembly
`canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing` already handles that order for
`CapWindowContinuation`; the lead should check that it also handles it for Crossing. Add B5 finding (i):
the `Cbirth` of `exists_standard_comparison_of_cap_window_trace` is Θ-independent in its proof but
published after Θ, while the extension step needs Θ = Θ(T, Q). It must be republished before Θ
(50–150 lines).

**M7 (gaps, small).**
- (a) B6a/B6b' hard-wire depth `k+2` and the ancient interval. The partial limit needs a depth
  schedule and an `openClosed` gluing variant (§4.1).
- (b) There is no `CapWindowPoint` monotonicity in `(Dcap, θcap)`; add it (about 20 lines).
- (c) B5 needs `u = tₙ − T/Rₙ ≥ 0`, i.e. `tₙRₙ → ∞`. This follows from the class (bounded initial
  curvature), but must be stated.
- (d) B5 on the terminal slab needs the `extendHorizon` transport of records and `CapWindowPoint`
  (B5 finding (ii)).

## 1. The contradiction sequence (inside the leaf proof; no new public theorem)

Negate `CrossingContinuation` after `εbar`, `B`, `ε ≤ εbar`, the canonical constants, `C1s C2s Cs`,
`κ`, `phi`, and `θ` are fixed. `εbar := min εcone εfar` is chosen before everything; this is "cone
accuracy before `qcan`", and the spatial witnesses are at accuracy `ε ≤ εbar`. Instantiate the
existentials with:
- `Dₙ = n + 1`, `θcapₙ = 1 − 1/(n + 2)`, `q₀ₙ = n + 1`, `mcapₙ = n`;
- `δmaxₙ = ρmaxₙ = εcapₙ = 1/(n + 1)`. After the M6 fix, `ρmaxₙ` is chosen after `qcanₙ` with
  `ρmaxₙ² ≤ Cbirth/(4·qcanₙ)`.

This yields, for each `n`:
- `qcanₙ ≥ n`, `qsₙ ∈ [qcanₙ, Cs·qcanₙ]`, `p₀ₙ`, `Hₙ`, `recordsₙ`, the family and class facts, and
  `EventSlabs{Canonical, Derivative, Gradient, SpatiallyCanonical}`;
- a slab (event `j` or terminal `G`), `t₀ₙ`, and the "before" data.
- For every `η` there is a violating `(y, t)`. B1 fixes `ηₙ` and `(yₙ, tₙ)` with:
  - `qcanₙ < Rₙ := R(yₙ, tₙ)` and `Rₙ(tₙ − aₙ) < θ`;
  - `¬CapWindowPoint recordsₙ _ yₙ tₙ Dₙ θcapₙ`;
  - one of the three `CanonicalBoundsOn` clauses fails at `(yₙ, tₙ)`.

Consequences:
- `Rₙ → ∞`.
- The normalized witness threshold is `qsₙ/Rₙ < Cs`.
- The noncollapsing is `NoncollapsedBefore κ ε t₀ₙ`. Its radius `ε` is fixed, so `ε√Rₙ → ∞`.

Write `seq` for this data. Every statement below is about `seq ∘ σ` for strictly monotone `σ`.

## 2. Maximal extendable depth (subsequence form), home `Surgery/Topology/TracedRegionMaximalDepth.lean`

```lean
def ObservedHistory.DepthExtendable (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (σ : ℕ → ℕ) (T : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in atTop,
    (H (σ i)).isTracedRegion (t (σ i)) (y (σ i)) (A / √(R (σ i))) (T / R (σ i)) (K * R (σ i))

theorem DepthExtendable.mono_depth : DepthExtendable H t y R σ T → 0 < T' → T' ≤ T →
    DepthExtendable H t y R σ T'                              -- isTracedRegion.mono_depth
theorem DepthExtendable.comp : DepthExtendable H t y R σ T → StrictMono ψ →
    DepthExtendable H t y R (σ ∘ ψ) T                           -- Tendsto.eventually of ψ

theorem exists_strictMono_maximal_of_antitone_subseq_property      -- generic, Order/Filter
    (E : (ℕ → ℕ) → ℝ → Prop) (hdown : ∀ σ T T', 0 < T' → T' ≤ T → E σ T → E σ T')
    (hsub : ∀ σ ψ T, StrictMono ψ → E σ T → E (σ ∘ ψ) T)
    (htail : ∀ σ σ' T, (∀ᶠ i in atTop, σ i = σ' i) → E σ T → E σ' T) :
    ∃ σ, StrictMono σ ∧ ∀ ψ, StrictMono ψ → ∀ T, E (σ ∘ ψ) T → ∀ T' < T, 0 < T' → E σ T'
```
The last lemma is proved by a diagonal argument: `σ_{k+1} ⊆ σ_k` with
`T*(σ_{k+1}) ≥ sup_{σ' ⊆ σ_k} T*(σ') − 2^{-k}`, then `σ∞ k := σ_k k`.
`DepthExtendable` needs the eventual-agreement form `htail`, because `σ∞` is only eventually a
subsequence of each `σ_k`. Size 150–300 lines.

With `σ∞` fixed, set `T* := sSup {T | DepthExtendable … σ∞ T} ∈ (0, ∞]`. It is positive by §3.3 and
maximality. Maximality means that no `σ∞ ∘ ψ` is extendable at any depth above `T*`.

## 3. Base case `T* > 0`

### 3.1 B3e — bounded curvature at distance on an arbitrary history slice (blocker, M1)

```lean
theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_spatially_canonical_slice
    (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∃ εcone : ℝ, 0 < εcone ∧ ∀ ε ≤ εcone, ∀ A > 0, ∀ Cq : ℝ, ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
    ∀ (P₀) (H : RetainedCoreHistory P₀) (p₀ δbound ρbound) (p) (records) (hrec : H.IsCanonicalCutoffRecordFamily …)
      (v : Icc (0 : ℝ) H.horizon) (y : (H.stageAt v).Carrier) (q ρ : ℝ),
      let g := H.toHistory.stageMetric (H.toHistory.activeStage v) v
      0 < q → q ≤ Cq * metricScalarAt g y → Λ ≤ metricScalarAt g y →
      (∀ x, q < metricScalarAt g x → ∃ W : SpatialCanonicalWitness g ε C1 C2 x, W.capTubeHasNeckChart ε) →
      H.EventSlabsDerivative Ctime q (H.toHistory.activeStage v) → (current-slab DerivativeBoundBefore Ctime q v) →
      (current-slab GradientBoundBefore Cgrad q v) → H.EventSlabsGradient Cgrad q _ → H.EventSlabsPinched phi →
      (final-slab pinching) → H.NoncollapsedBefore κ ρ v → Λ ≤ ρ * √(metricScalarAt g y) →
      ∀ z ∈ riemannianBallOf g y (A / √(metricScalarAt g y)), metricScalarAt g z ≤ Q * metricScalarAt g y
```
Delta from B3d:
- No final-slab window. Records and class data are added so the per-point X2 dichotomy is available
  (`BackwardTraceDistortion.lean:716`; cap points take their jets from the record, as in
  `CapWindowDerivativeBounds`).
- Terminal-slab uses go through `extendHorizon`, as B7 does.
- The same `εcone` as B3d.

Rebased form, used for `hRP` (proof: B3d's intermediate-value rebasing to a point with
`R = max(q, Λ, R(z))`):
```lean
theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_bounded_point_slice … :
    ∀ A D : ℝ, ∃ C, ∀ … (v) (z x) (Rn : ℝ), q ≤ Cq * Rn → Λ ≤ Rn → Λ ≤ ρ * √Rn →
      metricScalarAt g z ≤ A * Rn → riemannianEDistOf g z x < ofReal (D / √Rn) →
      metricScalarAt g x ≤ C * Rn
```
Size: 2.5–5k lines, of which the first-level compactness without window is 1.5–3k.

### 3.2 Time-zero spatial limit and its whole-slice bound

**3.2a, far field at a single slice.** Generic Riemannian statement, home
`Perelman/CanonicalNeighborhood/SpatialScalarBound.lean`. It is the port of
`BackwardScalarExterior.lean:89` at `A = 0`.
```lean
theorem exists_scalar_bound_of_complete_sectional_nonnegative_of_spatialCanonicalWitness :
    ∃ εfar : ℝ, 0 < εfar ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
      (g : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g → SecLower g 0 univ →
      ∀ {ε C1 C2 q : ℝ}, ε ≤ εfar →
      (∀ x, q < metricScalarAt g x → ∃ W : SpatialCanonicalWitness g ε C1 C2 x, W.capTubeHasNeckChart ε) →
      ∃ C, ∀ x, metricScalarAt g x ≤ C
```
Proof:
- The compact case follows from continuity.
- In the noncompact case, at a far high point `y`:
  - the whole-component alternative is excluded, because the component contains `p` at distance
    `> R` while its diameter is `≤ C/√R(y)` (`SpatialCanonicalWitness.eq_connectedComponent_of_isWholeComponent`,
    `SpatialBoundedCurvatureAtDistance.lean:115`);
  - a cap gives a neck centre `y'` from the tube chart, with `d(y, y') ≤ C/√R(y)` and
    `R(y') ≥ R(y)/C` (as in B3c's `nonempty_spatialNeck_of_minimizing_segment`).
- Then apply `exists_far_spatialNeck_unbounded_separated_component_of_nonnegative`,
  `exists_uniform_spatial_neck_core_diameter`, and the path-connected ball complement (port of
  `TerminalLimit.exists_uniform_pathConnected_ball_complement`), exactly as in the template.

The distance-comparable version used in §4.2 has the same proof with the `herror` hypothesis kept.
Together 0.7–1.2k lines.

**3.2b, time-zero bound along the sequence.** Home `Surgery/Topology/CrossingMaximalWindow.lean`.
```lean
theorem exists_subseq_scalar_le_on_normalized_balls_at_base (seq …) (σ) (hσ : StrictMono σ) :
    ∃ ψ, StrictMono ψ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A > 0, ∀ᶠ i in atTop,
      ∀ z ∈ riemannianBallOf (g (σ (ψ i)) at t) (y (σ (ψ i))) (A / √(R (σ (ψ i)))),
        metricScalarAt _ z ≤ C₀ * R (σ (ψ i))
```
Proof:
1. B3e at `tₙ`, with `Cq = Cs`, gives `Q(A)`.
2. B7's step and B5 at depth `1/(2·Ctime·Q(A))` give per-`A` traced regions. From them come the
   Shi jets and the κ tests (B6b's internals).
3. `exists_pointed_convergence_on_base_components_of_eventually_compact_balls` (B6a file 1) gives a
   complete connected limit `P₀`.
4. `Rm ≥ 0`, from `rescalePinchingFunction Rₙ phi → 0`.
5. Witness transport to `P₀` (`SpatialCanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn`,
   `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessComparisonTransport.lean:146`, plus
   `capTubeHasNeckChart.pushforward`) at accuracy `2ε`, above `Cs + 1`.
6. §3.2a gives `C`; set `C₀ := 2C + 1` and pull it back to the normalized balls.

Size 400–700 lines.

### 3.3 Base extendability
```lean
theorem exists_subseq_depthExtendable_pos (seq …) (σ) (hσ : StrictMono σ) :
    ∃ ψ, StrictMono ψ ∧ ∃ T₀ > 0, DepthExtendable H t y R (σ ∘ ψ) T₀
```
With `Q := 2C₀` and `T₀ := 1/(4·Ctime·C₀)`, B7's `scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball`
gives B5's `hscal`. Apply B5 (`TracedRegionOrCapWindow.lean:665`) with:
- `T := T₀`;
- `θcap := max (1/4) (1 − c/(8·T₀·Q))`, and `Θ := (θcap + 1)/2`;
- `Dcap := D(A, T₀, Q) + 1`, and `Dstar := Dcap`.

The right branch implies `CapWindowPoint Dₙ θcapₙ` for large `n` (M7b), which contradicts badness.
The conditions hold eventually:
- `Rrad ≤ modelRadius`;
- `m₀ ≤ n`;
- `modelAccuracy ≤ 1/n ≤ ζ₀`;
- `δbound ≤ δ₀`;
- `hbirth` and `ha₀` (after M6).

Size 250–400 lines.

## 4. The finite `T*` case

### 4.1 Partial limit on `(−T*, 0]` (B6a/B6b' with a depth schedule)

- **Generic B6a**, `Compactness/Limits/AncientPointedFlowLimit.lean`. Add a depth schedule `τ : ℕ → ℝ`
  (`StrictMono τ`, `0 < τ 0`, `Tendsto τ atTop (𝓝 T)`, or `atTop` for the ancient case).
  - Change `hsol` to `closed (−τ (k+1)) 0` and `hjets` to `Icc (−τ k) 0`.
  - The output is `G` on `openClosed (−T) 0 0 _`, or on `infiniteClosed 0 0` in the ancient case,
    with convergence on compacts of `V k × Icc (−τ k) 0`.
  - Gluing: generalize `exists_ancient_solution_of_compatible_open_cover`
    (`Solution/AncientGluing.lean:17`) to windows `Icc (−τ n) 0`. `exists_metric_family_of_compatible_open_covers`
    is already window-generic, and `isSolutionOn_of_closed_backward_windows` needs an `Ioc` analogue.
  - The existing ancient theorem becomes the instance `τ k = k + 1`.
  - Size 400–700 lines.
- **B6b' windowed**, `Surgery/Topology/TracedRegionAncientLimitData.lean`.
  `htraced` becomes `∀ A T, 0 < A → 0 < T → T < Tstar → ∃ K ≥ 0, ∀ᶠ n, isTracedRegion …`, the depth
  schedule is `τ k := Tstar·(k+1)/(k+2)`, and the conclusions (i)–(v) are unchanged. Size 150–300
  lines of edits.

### 4.2 Properties and the uniform bound near `−T*`

On `G : ℝ → SmoothRiemannianMetric I3 P.M` with `IsSolutionOn` on `openClosed (−T) 0 0 _` and
`G 0 = P.metric`:

| Fact | Supplier or new work | Lines |
|---|---|---|
| `Rm ≥ 0` for `s ∈ Ioc (−T) 0` | window version of `curvatureOperator_nonnegative_of_local_pinching_limit` (`AncientPointedFlowLimitCurvature.lean:26`) | 60–120 |
| every slice complete | `complete_at_earlier_time_of_ricci_nonnegative` on `[s, 0]` | 40–80 |
| spatial witnesses above `Cs + 1`, accuracy `2ε` | transport as in §3.2b | 200–400 |
| `hderiv`: `|∂ₜR| ≤ Ctime R²` where `R > 1` | approximants' `EventSlabsDerivative` / `DerivativeBoundBefore` above `qcanₙ < Rₙ`, via `scalar_evolution_of_smooth_solution` (`Evolution/Scalar/Basic.lean:91`) and the spatial `C^p` convergence | 250–500 |
| `hRP`: `∀ A D, ∃ C, ∀ s ∈ Ioc (−T) 0, ∀ z x, R(z,s) ≤ A → d_s(z,x) ≤ D → R(x,s) ≤ C` | rebased B3e at slice `tₙ + s/Rₙ`, pulled through the survivor maps (B6b' (iv), injective local isometries, so stage distance ≤ `W`-distance); event-time slices by continuity in `s` | 300–500 |

**Time-zero global bound** (§3.2a applied to `G 0 = P.metric`):
```lean
theorem exists_scalar_bound_at_time_zero_of_spatialCanonicalWitness … : ∃ Q₀, ∀ x, metricScalarAt P.metric x ≤ Q₀
```

**Uniform bound on the window** (the "bound near the finite end", M4). Home
`Perelman/CanonicalNeighborhood/WindowScalarBound.lean`; it is generic and needs no history.
```lean
theorem exists_uniform_scalar_bound_on_openClosed_window_of_spatialCanonicalWitness :
    ∃ εfar : ℝ, 0 < εfar ∧ ∀ {P : PointedRiemannianManifold.{u,0,0} I3} [ConnectedSpace P.M]
      {T : ℝ} (hT : 0 < T) (G : ℝ → SmoothRiemannianMetric I3 P.M),
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.openClosed (-T) 0 0 ⟨by linarith, le_rfl⟩)) → G 0 = P.metric →
      (∀ s ∈ Ioc (-T) 0, RiemannianMetricComplete (G s)) →
      (∀ s ∈ Ioc (-T) 0, ∀ x, metricAlgebraicCurvatureTensorAt (G s) x ∈ algebraicCurvatureOperatorNonnegativeCone) →
      ∀ {ε C1 C2 q : ℝ} {Ctime : ℝ≥0}, ε ≤ εfar →
      (∀ s ∈ Ioc (-T) 0, ∀ x, q < metricScalarAt (G s) x →
        ∃ W : SpatialCanonicalWitness (G s) ε C1 C2 x, W.capTubeHasNeckChart ε) →
      (∀ s ∈ Ioo (-T) 0, ∀ x, q < metricScalarAt (G s) x →
        |derivWithin (fun v => metricScalarAt (G v) x) (Iic s) s| ≤ Ctime * metricScalarAt (G s) x ^ 2) →
      (∀ A D : ℝ, ∃ C, ∀ s ∈ Ioc (-T) 0, ∀ z x, metricScalarAt (G s) z ≤ A →
        metricDistance (G s) z x ≤ D → metricScalarAt (G s) x ≤ C) →
      ∃ C, ∀ s ∈ Ioc (-T) 0, ∀ x, metricScalarAt (G s) x ≤ C
```
Proof (bootstrap):
1. Set `Q₀` from the time-zero bound, and `S := {a ∈ Ioo (−T) 0 | whole-slice bound on Icc a 0}`.
   The curvature-norm form follows from `Rm ≥ 0`.
2. **Uniform constant.** For `a ∈ S`:
   - `ricciFlow_additive_distance_bound_of_terminal_scalar` on `[a, 0]` gives
     `d_0 ≤ d_s ≤ d_0 + A_H` with `A_H := (20/3)√(2TQ₀)√T`, independent of `a`.
   - Noncompact slice: the far-field bound under `A_H`-comparability (port of
     `BackwardScalarExterior.lean:89`, §3.2a) gives `R ≤ Cfar` outside `B_0(p, R_far)`. At an escape
     point `z`, `hRP` with `(Cfar, d_0(z, p) + R_far + A_H)` bounds the rest.
   - Compact slice: port `exists_uniform_scalar_bounded_point_and_diameter_of_compact`
     (`BackwardFiniteHorizon.lean:73`) and apply `hRP`.
   - This gives `C*` independent of `a`. It is the template `BackwardScalarBound.lean:22`, verbatim in
     structure.
3. **Step.** For `a ∈ S`, `hderiv` gives the bound `2·max(C*, q)` on `[a − δ, a]`, with
   `δ := 1/(2·Ctime·max(C*, q))`. The step also gives `−δ ∈ S` from `Q₀`.
4. Hence `S = Ioo (−T) 0`, with the bound `2·max(C*, q)` throughout.

Size 500–900 lines, plus the far-field port counted in §3.2a.

κ on the partial limit: nothing above uses it, because the witnesses are spatial. B6c-κ (the
reference-conversion route, digest item 3) is needed only in §5, and only on the ancient limit.

### 4.3 Extension: `T*` is not maximal
```lean
theorem exists_subseq_depthExtendable_beyond_of_window_bound (seq …) (σ) (hσ : StrictMono σ)
    {Tstar : ℝ} (hT : 0 < Tstar) (hext : ∀ T, 0 < T → T < Tstar → DepthExtendable H t y R σ T)
    (partial-limit data from §4.1 along σ ∘ ψ) {C : ℝ} (hC : ∀ s ∈ Ioc (-Tstar) 0, ∀ x, G.scalar s x ≤ C) :
    ∃ ψ', StrictMono ψ' ∧ DepthExtendable H t y R (σ ∘ ψ')
      (Tstar + 1 / (32 * Ctime * (C + 1)))
```
Proof:
1. Set `M := 2(C+1)`, `Δ := 1/(8·Ctime·M)`, `T' := Tstar − Δ/2` (if `T' ≤ 0`, then
   `T' := Tstar/2`), and `T := T' + Δ`. The gain `Δ/2` does not depend on `A`.
2. Fix `A`.
   - The traced region at `(A, T')` gives the bound `√3·K(A,T')·Rₙ` along traces on
     `[tₙ − T'/Rₙ, tₙ]` (`isTracedRegion.normSq_le`, `scalar_abs_le_rm`).
   - Anchor: the trace point at `uₙ := tₙ − T'/Rₙ` equals `f_j x` (`point_unique`, B6b' (iv)).
     `C^0` convergence on `B̄(A) × {−T'}` gives `R ≤ M·Rₙ` there.
   - Step: `scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_at` (`TracedRegionBackwardStep.lean:121`,
     `htime` holds by the choice of `Δ`) gives `R ≤ 2M·Rₙ` on `[uₙ − Δ/Rₙ, uₙ]`.
   - Hence B5's `hscal` holds with `Q := max(√3·K, 2M)/2` at depth `T`.
3. Apply B5 with `θcap := max(1/4, 1 − c/(8TQ))` and `Dcap := D(A,T,Q) + 1`. The right branch
   contradicts badness through M7b, so the region is traced with `K' = 8√3(1+φ1+φ0)Q`.

Since `T > Tstar`, this contradicts the maximality of `σ∞` (§2). Therefore `T* = ∞`. Size 300–500 lines.

## 5. `T* = ∞`: the ancient limit and the contradiction

1. `DepthExtendable σ∞ T` for all `T` is B6b's `htraced` along `σ∞`. B6b'
   (`TracedRegionAncientLimitData.lean:321`) gives `G` on `(−∞, 0]` with survivor maps,
   `IsSolutionOn (h k n)`, and the κ tests.
2. B6c: `Rm ≥ 0` and complete slices (`AncientPointedFlowLimitCurvature.lean:122`).
3. **B6d, global bound.**
   - For every `T`, the §4.2 theorem on `G|(−T, 0]` gives whole-slice bounds on compact windows.
     Its inputs `hW`, `hderiv`, `hRP` are the §4.2 transfers.
   - `hamilton_ancient_scalar_le_terminal` (`HamiltonHarnack/TerminalScalar.lean:103`, with `hcurv`
     from the step before, `hR` from `Rm ≥ 0`, `hcomplete` from B6c) then gives `R(G t) ≤ R(G 0) ≤ Q₀`.
   - This yields `PointedFlowScalarBounded` with constant `Q₀`. Size 150–300 lines.
4. B6c-κ (separate lane, reference conversion) gives `ParabolicallyKappaNoncollapsedBelowScale` at
   every scale. `isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative`
   (`AncientPointedFlowLimitCurvature.lean:185`) then gives `IsAncientKappaSolution (κ/30³)` with
   scalar 1 at the base.
5. B8 (`AncientLimitCanonicalWitness.lean:117`, `:533`, `:29`), together with B0/B1 and the orientation
   of the limit (B8 input (b)), gives eventually all three `CanonicalBoundsOn` clauses at
   `(yₙ, tₙ)` along `σ∞ ∘ ψ`. This contradicts the choice of `(yₙ, tₙ)`. Size 400–800 lines of
   assembly.

## 6. Order and size

1. G0 (§2) and M7b: 0.2–0.35k lines.
2. M6 statement fix and B5's `Cbirth` republish: 0.05–0.15k lines.
3. B3e (§3.1): 2.5–5k lines. This is the critical path.
4. Far-field port (§3.2a): 0.7–1.2k lines.
5. Time-zero limit (§3.2b) and base case (§3.3): 0.65–1.1k lines.
6. Windowed B6a/B6b' (§4.1): 0.55–1k lines.
7. Transfers and bootstrap (§4.2): 1.35–2.5k lines.
8. Extension (§4.3): 0.3–0.5k lines.
9. B6d via Harnack and the §5 assembly: 0.55–1.1k lines.

Total about 7–13k lines, excluding B6c-κ, B0/B1 and B8b.

Items 1, 2, 4 and 6 are parallel now. Item 3 blocks items 5 and 7. Items 8 and 9 come last.
