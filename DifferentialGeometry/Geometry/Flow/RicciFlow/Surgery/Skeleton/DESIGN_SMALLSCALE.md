# Small-scale noncollapsing leaf: design (2026-09-26)

Scope: `SmallScaleNoncollapsingThroughSurgery` (`Surgery/Topology/NoncollapsingThroughSurgeryLeaves.lean:147`).
Worktree `D:\differential-geometry-pc3`, branch `codex/pc-target-c-psf`. HEAD moved while I worked
(0798da941 → bf07a1e58 → 9126abc30). Read-only design: no Lean edits, no git writes, no builds.
Every statement in §3 was elaborated with `sorry` bodies in one scratch probe outside the repo
(`LEAN_NUM_THREADS=2 lake env lean`). Result: 7 declarations, **0 errors**, only `sorry` warnings.

## 1. Failures and deviations first

1. **FALSE: the round alternative gives no volume.** `SpatialCanonicalWitness.volume` is guarded by
   `alternative.requiresVolume`, and `SpatialCanonicalAlternative.requiresVolume (.round _ _) = False`
   (`Perelman/CanonicalNeighborhood/SpatialCanonicalWitness.lean:101,121`). Counterexample to any
   "witness ⇒ ball volume" lemma: take a component `U = S³/ℤₙ` with a round metric of scalar `Q`.
   `.round` holds with `Z = U` and `map = id`, and `metric_bounds` holds with factor 1. The ball
   `B(x, Q^{-1/2})` satisfies `r⁴|Rm|² ≤ 1`, but its volume is `≤ vol U = O(Q^{-3/2}/n) → 0`.
   The leaf's other inputs do not rule this out when `Q ≫ r₀⁻²`: no ball of radius `≥ r₀` is
   Rm-controlled there, so `NoncollapsedAboveBefore` says nothing. The leaf *statement* is not refuted,
   because the whole class history is a hypothesis. The digest's trichotomy proof, however, cannot close
   the round case. Two interface repairs fail on quantifier order:
   - C4 cannot add a round-volume clause, because `C1s C2s` are chosen before `κ`, and round κ-solutions
     are not uniformly noncollapsed (Perelman II 1.5 excepts round quotients).
   - A clause with a `κ`-dependent constant is circular: it would need `κ₂ ≤ c·min(κ_red, κ₂)`.

   **Needs a lead decision (§5).** All other cases are designed below.
2. **The digest's sup-trichotomy is replaced by KL's dichotomy on `R(p,t)`.** The tree already
   contains its low-curvature half, but with no consumer:
   `exists_parabolicallyRmControlledBall_or_capWindowPoint` (`Surgery/Topology/BackwardTraceDistortion.lean:642`)
   and `…_of_activeStage_eq_last` (`BackwardTraceDistortionTerminal.lean:517`). Both give parabolic
   control at radius `c/√R(y)` through events, or else a young cap-window point. The radius has to be
   the fixed `r₀`, not one set by `R(y)`, so both need a threshold-`M` generalization (S1).
   The sup machinery (`csSup_parabolicallyRmControlledBall_mem_Icc`, `HistoryParabolicBall.lean:191–260`)
   is not needed.
3. **Case A normalization.** The controlled ball of radius `r₀` gives `|Rm| ≤ r₀⁻²`, so
   `Ric ≥ −9 r₀⁻² g` (`ricciLowerAt_of_rm`, dimension factor `n² = 9`). In
   `bishop_gromov_of_isCompact_closedEBall` (`Geometry/Comparison/Volume/Bishop/CompactBall.lean:162`)
   this is `q = 3/(√2 r₀)`. Then `hyperbolicRadialVolume_ratio_le`
   (`Geometry/Comparison/Volume/Segment/Count.lean:110`) gives
   `vol B(r) ≥ e^{-3√2}(r/2r₀)³ vol B(r₀)`, so `cBG = e^{-3√2}/8` is universal.
   - Missing: a `riemannianBallOf`-level wrapper with a Ricci bound only on the ball. The existing
     wrapper, `riemannianBallOf_volume_bishop_nonnegative`
     (`Perelman/KappaSolutions/AsymptoticVolumeRatio.lean:136`), needs a global `Ric ≥ 0`. New brick S3.
4. **The event-time slice (I28 gap, DESIGN_28 item 6) needs no witness at `t₀` or at post-surgery
   slices.** A generic transfer lemma S0 moves every slice to a regular time `t' ∈ [t−θr², t−θr²/2]`:
   `t'` is not an event time and satisfies `t' < t ≤ t₀`, so the age-free spatial, derivative and
   gradient clauses are all available there. The cost is one universal factor `c_T`.
   - Fresh cap points never lie in a parabolically controlled ball, because they have no backward
     trace (review item 6). The standard-solution witness of 27c is therefore **not** needed.
   - Platform: `exists_common_flow_with_compact_neighborhood_of_parabolicallyRmControlledBall`
     (`HistoryParabolicBall.lean:860`). It gives one smooth `SolutionOn` over `[t−r², t]` on
     `U = B_t(p,r)`, through all crossings, with `|Rm| ≤ r⁻²` and a compact `r/2`-ball.
5. **`qs ≤ Cs·qcan` is irrelevant and compatible.** The leaf only uses `qcan ≤ qs`: derivative and
   gradient bounds apply where `R > qcan`, and `M := max qs (1/4) ≥ qcan`. `r₀` is chosen after
   `qcan qs` (`∃ r₀` follows `∀ qcan qs`), so `r₀ ≤ c/√M` is legal. `κ` precedes `qcan qs` and
   depends only on `κ₁`, `(ε, C1s, C2s)`, `g₀` and universal constants.
6. **Early layer.** `t ≤ η` needs its own brick S6: there the `r ≥ r₀` clause is vacuous, since
   `r² ≤ t < r₀²` is impossible. S6 also needs a class fact: no event occurs before `η(g₀)` when
   `ρbound ≤ ρ₁(g₀)`. It follows from
   - the uniform initial curvature bound (`exists_uniform_initial_curvature_bound`, `InitialSlabUniformBounds.lean:21`);
   - the record neck scale `> (2ρbound²)⁻¹` (`IsCanonicalCutoffRecordFamily.inv_two_mul_sq_lt_static_scale`, DESIGN_28 (iv)).

   Unverified: whether the record neck scale controls the terminal curvature strongly enough. Budgeted as a sub-brick.
7. **Witness volume is on the domain, not on a ball.** Therefore the cap case needs the neck chart
   supplied by `capTubeHasNeckChart ε`. The clause carries it: the tube equals `nk.map` on
   `S²×[0,1]`, with `nk : SpatialNeck g ε v`. Without that chart the cap core could be collapsed next to
   a fat tube.

## 2. Proof of the leaf (regular-time dichotomy)

For a regular time `t` (`t < t₀`, `t ≠ H.time i` for all `i`) and a controlled ball `(t, p, r)` with
`r ≤ r₀`, split on `R(p,t)` against `M := max qs (1/4)`:

- **Early** (`t ≤ η`): S6 gives `κ_init(g₀)`.
- **Low** (`η < t`, `R(p,t) ≤ M`):
  - S1 gives control at `c/√M ≥ r₀`; S2 excludes the cap-window alternative, because
    `(Cw + Ctime θcap)M < scale`.
  - `mono_radius` then gives control at `r₀`, and `NoncollapsedAboveBefore κ₁ r₀ ε t₀` at radius `r₀`
    gives `vol B(p,r₀) ≥ κ₁ r₀³`.
  - `terminal_curvature_bound` gives the spatial `|Rm| ≤ r₀⁻²` on `B_t(p,r₀)`; S3 then gives
    `vol B(p,r) ≥ cBG κ₁ r³`.
- **High** (`R(p,t) > M ≥ qs`):
  - The witness comes from `EventSlabsSpatiallyCanonical` (slab `i < j`) or from the current
    `SpatiallyCanonicalBefore t₀` (slab `j`, since `t ∈ Ioo`).
  - The control gives `r⁴|Rm|²(p) ≤ 1`, so S4 gives `κ_W(ε, C1s, C2s) r³` when `requiresVolume` holds.
    Round is **open** (§5).

S7 assembles these cases, and S0 lifts the result to `NoncollapsedBefore (c_T·κ) r₀ t₀`. The terminal
half is the same argument applied to `H.extendHorizon T …`: use the `_of_activeStage_eq_last`
variants, `hasCanonicalCutoffRecords_extendHorizon`, and `G.…Before t₀` for `t ∈ (time last, T)`.

Constants, in quantifier order:
- Before `qcan qs`:
  - `c := min (1/(4·max Cgrad 1)) (min ((8·max Ctime 1)^{-1/2}) ((3072(1+φ1+φ0)²)^{-1/4}))`, from
    `hcgrad`, `hctime` and `hcpinch` of `BackwardTraceDistortion.lean:642`;
  - `κ := c_T · min (min (cBG·κ₁) κ_W) κ_init`.
- After `qcan qs`:
  - `M := max qs (1/4)`, `r₀ := min (min ε (c/√M)) (min (√η) 1)`;
  - `θcap := 16c²`, `Dcap := 2·transitionEnd + √32·c·exp(288√3(1+φ1+φ0)c²) + 1`, `Dstar := Dcap`;
  - `εcap := min (1/2) (min ε₀^{scalar}(Dcap) ε₀^{window}(Dcap))`, with `ε₀^{scalar}` from
    `exists_presented_cap_scalar_lower_bound_of_canonical_window_core` (`CanonicalCapScalar.lean:70`)
    and `ε₀^{window}` from S2a;
  - `mcap := 2`, `δmax := 1`, `ρmax := min ρ₁ (2(Cw + Ctime·θcap)M)^{-1/2}`.

## 3. Exact statements (all elaborate; namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`)

Probe preamble: the imports are `…Topology.NoncollapsingThroughSurgeryLeaves`,
`…Topology.BackwardTraceDistortion` and `DifferentialGeometry.Geometry.Neck.BallVolume`, with
`open … DifferentialGeometry.Tensor0SBundle`, plus the leaf file's `private local instance`
`MeasurableSpace`.

**S0-def**
```lean
def RetainedCoreHistory.NoncollapsedAtRegularTimesBefore (H : RetainedCoreHistory P₀) (κ ρ t₀ : ℝ) : Prop :=
  ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
    (t : ℝ) < t₀ → (∀ i : Fin (H.eventCount + 1), H.time i ≠ t) → r ≤ ρ →
    H.toHistory.isParabolicallyRmControlledBall t p r →
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r)
```
**S0 (slice transfer)**
```lean
theorem exists_noncollapsedBefore_of_regularTimes :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ {P₀ : OrientedThreeStage.{u}} (H : RetainedCoreHistory P₀)
      {κ ρ t₀ : ℝ}, 0 < κ → H.NoncollapsedAtRegularTimesBefore κ ρ t₀ →
        H.NoncollapsedBefore (c * κ) ρ t₀
```
Proof route:
1. Choose `θ ≤ 1/2` and a regular `t'` in `[t − θr², t − θr²/2]`; `t'` is positive, and the set of
   event times is finite.
2. Take the common flow `S` on `U` from `HistoryParabolicBall.lean:860`, and set `p' := f_{stage t'} p`.
3. Show `B_{t'}(p', r/L) ⊆ f(K)` by continuity along paths, using the metric distortion
   `inner_le_exp_mul_inner_of_rmNormSq_le` (`Perelman/Noncollapsing/ForwardTransfer.lean:91`) and the
   compactness of `K`.
4. The control at `(t', p', r/L)` follows by restricting the traces (`isRmControlled.restrictFirst`
   and a `restrictLast` analogue).
5. The volume bound at `t` follows from `volume_riemannianBallOf_le_exp_mul_of_rmNormSq_le`
   (`ForwardTransfer.lean:126`) on `S`, because `f` is an injective local isometry.

**S1 (low-curvature control, threshold `M`)** is a generalization of `BackwardTraceDistortion.lean:642`. Probed with:
```lean
theorem RetainedCoreHistory.exists_isParabolicallyRmControlledBall_or_capWindowPoint_of_scalar_le
    {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan M c Dcap θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hqM : qcan ≤ M) (hM : 1 ≤ 4 * M)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    {u : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hu : (u : ℝ) = t - c ^ 2 / M)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hgrad : ∀ w, qcan < (H.toHistory.event i).incoming.flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.toHistory.event i).incoming.flow t w v| ≤
          Cgrad * (H.toHistory.event i).incoming.flow.scalar t w *
            Real.sqrt ((H.toHistory.event i).incoming.flow.scalar t w) *
            Real.sqrt (((H.toHistory.event i).incoming.flow.base.metric t).inner w v v))
    {Dstar : ℝ} (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap) :
    H.toHistory.isParabolicallyRmControlledBall t y (c / Real.sqrt M) ∨
      H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap
```
Plus a `…_of_activeStage_eq_last` twin, copied from `BackwardTraceDistortionTerminal.lean:517`.
Supply at a regular `t < t₀`:
- `hslabs` comes from `EventSlabsDerivative … j.castSucc`, by monotonicity in `k`;
- `hcurrent` comes from `derivativeBoundBefore_mono`, either from slab `i`'s `time i.succ` or from `t₀`;
- `hgrad` at `t` comes from `GradientBoundBefore`, because `t ∈ Ioo`;
- `records` and `hcan` come from `hH.2.2.2.1`, and `hscale` from `CanonicalCapScalar.lean:70`.

**S2 (young caps are hot)**
```lean
theorem RetainedCoreHistory.not_capWindowPoint_of_scalar_le {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    {Ctime : ℝ≥0} {qcan M Cw Dcap θcap : ℝ} (hqM : qcan ≤ M) (hCw : 1 ≤ Cw)
    (hwinScale : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
      ((records j).static b).neck.scale / Cw ≤
        metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x))
    (hbig : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
      (Cw + Ctime * θcap) * M < ((records j).static b).neck.scale)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t) :
    ¬ H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap
```
Proof: along the trace `A` of `CapWindowPoint`, `1/R` grows by at most `Ctime` per unit time, and
crossings preserve `R`. That gives `1/R(y,t) ≤ Cw/scale + Ctime·θcap/scale < 1/M`.
- **S2a** proves `hwinScale` with `Cw` from `StandardCap.exists_uniform_window_scalar_bounds_of_metric_close`,
  in the same way as `CanonicalCapScalar` (v).
- `hbig` follows from `inv_two_mul_sq_lt_static_scale` and the choice of `ρmax`.

**S3 (local Bishop–Gromov)**
```lean
theorem exists_riemannianVolumeMeasure_ball_ge_of_rm_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p : P.Carrier) {r R : ℝ},
      0 < r → r ≤ R →
      (∀ x ∈ riemannianBallOf g p R, R ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) →
      ENNReal.ofReal (c * (r / R) ^ 3) *
          riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p R) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r)
```
Proof:
- Use the instance setup of `AsymptoticVolumeRatio.lean:136` and `bishop_gromov_of_isCompact_closedEBall`.
- The closed ball is compact because `P` is compact.
- The Ricci bound comes from `ricciLowerAt_of_rm`, and the ratio from `hyperbolicRadialVolume_ratio_le`.

A `q = 0` variant, with `Ric ≥ 0` on the ball, is needed for the positive case of S4.

**S4 (witness ⇒ ball volume, non-round)**
```lean
theorem exists_ball_volume_of_spatialCanonicalWitness (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      W.alternative.requiresVolume → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x r)
```
- **Neck.** Already proved: `exists_pos_mul_cube_le_spatialNeck_ball_volume_of_curvature_bound`
  (`Geometry/Neck/BallVolume.lean:286`).
- **Positive.** `U` is a connected component, so `B(x,·) ⊆ U`, and `SecLower` gives `Ric ≥ 0`.
  - The volume clause gives `vol U ≥ C2⁻¹Q^{-3/2}`, and `U ⊆ B(x, 2C1Q^{-1/2})`.
  - The pointwise bound gives `r ≤ 3Q^{-1/2}`, via `scalar_abs_le_rm`.
  - S3 with `q = 0` then gives `κ = C2⁻¹/(8·27·C1³)`, up to the dimension constant.
- **Cap.**
  1. Let `w` be the nearest tube point, at distance `D ∈ [10⁴Q^{-1/2}, 2C1Q^{-1/2})` (deep clause).
     Then `B(x,D) ⊆ U`, because `frontier U ⊆ tube`.
  2. Set `s = Q_v^{-1/2}/2`. Then `B(x, D+s) ⊆ U ∪ nk.map(S²×(−ε⁻¹, ε⁻¹))`, using
     `CylinderReference.closedBall_subset_slab`.
  3. `|Rm| ≲ C2·Q` on that set, where the neck-chart bound comes from `MetricComparisonOn`.
  4. `vol B(w,s) ≳ Q^{-3/2}`, by `exists_pos_mul_cube_le_spatialNeck_normalized_ball_volume`
     (`BallVolume.lean:150`) at `z.2 ∈ [0,1]` with normalized radius `1/2`.
  5. S3 from `r ≤ 3Q^{-1/2} ≤ D` up to `D + s ≤ (2C1 + √C2)Q^{-1/2}` then gives `κ(C1, C2)`.
- **Round.** Excluded by `requiresVolume`; see §1.1.

**S6 (early layer)**
```lean
theorem exists_initial_layer_noncollapsed (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ κ η ρ₁ : ℝ, 0 < κ ∧ 0 < η ∧ 0 < ρ₁ ∧
      ∀ (B : ℝ) (p₀ : CutoffParameters) (δbound ρbound : ℝ), ρbound ≤ ρ₁ →
      ∀ H : RetainedCoreHistory P₀, H.InCutoffClass g₀ B p₀ δbound ρbound →
      ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier) (r : ℝ),
        (t : ℝ) ≤ η → r ≤ 1 → H.toHistory.isParabolicallyRmControlledBall t p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
            (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r)
```
Route:
- Take `η ≤ 1/K`, with `K` from `exists_uniform_initial_curvature_bound`. Then every flow ball with
  `r² ≤ t ≤ η` is `IsRmControlled` for the moving-ball definition. This matters, because the history's
  fixed-set control does **not** imply `FlowMetricBall.IsRmControlled`.
- Apply `exists_uniform_kappaNoncollapsed_initial_of_pos` with `ρ = 1` (`InitialSlabNoncollapsing.lean:123`).
- Show no event lies before `η` (sub-brick; §1.6).

**S7 (case assembly)**, a pure combination of the cases:
```lean
theorem RetainedCoreHistory.noncollapsedAtRegularTimesBefore_of_cases {κ₁ κH κ₀ cBG M η r₀ ε t₀ : ℝ}
    (hr₀ : 0 < r₀) (hr₀ε : r₀ ≤ ε) (hr₀η : r₀ ^ 2 ≤ η) (hr₀1 : r₀ ≤ 1) (hcBG : 0 < cBG)
    (hBG : ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p : P.Carrier) {r R : ℝ},
      0 < r → r ≤ R →
      (∀ x ∈ riemannianBallOf g p R, R ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) →
      ENNReal.ofReal (cBG * (r / R) ^ 3) *
          riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p R) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r))
    (habove : H.NoncollapsedAboveBefore κ₁ r₀ ε t₀)
    (hlow : ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier),
      (t : ℝ) < t₀ → (∀ i : Fin (H.eventCount + 1), H.time i ≠ t) → η < t →
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M →
      H.toHistory.isParabolicallyRmControlledBall t p r₀)
    (hhigh : ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier)
      (r : ℝ), (t : ℝ) < t₀ → (∀ i : Fin (H.eventCount + 1), H.time i ≠ t) →
      M < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p →
      H.toHistory.isParabolicallyRmControlledBall t p r →
      ENNReal.ofReal κH * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
          (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r))
    (hinit : ∀ (t : Icc (0 : ℝ) H.toHistory.horizon) (p : (H.toHistory.stageAt t).Carrier)
      (r : ℝ), (t : ℝ) ≤ η → r ≤ 1 → H.toHistory.isParabolicallyRmControlledBall t p r →
      ENNReal.ofReal κ₀ * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
          (riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p r)) :
    H.NoncollapsedAtRegularTimesBefore (min (min (cBG * κ₁) κH) κ₀) r₀ t₀
```
It is true as stated. The low case uses `habove` at radius `r₀`, `terminal_curvature_bound` and `hBG`.

## 4. Bricks in dependency order (line estimates)

| # | Brick | Suppliers | Lines |
|---|---|---|---|
| 1 | S3 local BG (+ `q = 0` variant) | CompactBall:162, Count:110, `ricciLowerAt_of_rm` | 150–250 |
| 2 | S7 case assembly | S3, `terminal_curvature_bound`, `mono_radius` | 80–120 |
| 3 | S2a window scalar bound, then S2 (+ last-stage twin) | `exists_uniform_window_scalar_bounds_of_metric_close`, trace scalar lemmas (`BackwardTraceScalarTime`) | 200–330 |
| 4 | S1 threshold-`M` dichotomy (+ last-stage twin) | copy-generalize BackwardTraceDistortion:642 and Terminal:517, including the private helper | 200–300 |
| 5 | S4 neck / positive / cap | BallVolume:150,286, CylinderBallCapture, S3 | 600–800 (cap ≈ 450) |
| 6 | S6 early layer + no-early-event | InitialSlabUniformBounds:21, InitialSlabNoncollapsing:123, DESIGN_28 (iv) | 200–350 |
| 7 | S0 slice transfer | HistoryParabolicBall:860, ForwardTransfer:91,126 | 350–600 |
| 8 | Leaf wiring: hypothesis translation (stageMetric ↔ incoming flow, `extendHorizon` half, records from `hH`, constants) | `stageMetric_castSucc_apply`, `hasCanonicalCutoffRecords_extendHorizon` | 300–450 |
| – | Round case | open (§5) | ? |

Total without the round case: about 2100–3200 lines.

## 5. Decision needed: round components

The leaf can be closed, apart from round components, with the bricks above. For round components (the
`.round` alternative at `R > qs`), the witness carries no volume, and I found no κ-independent supply.
Candidate routes:
- **(a) Backward persistence, in the leaf.** Follow the ε-round component back until `R ≈ c²r₀⁻²`.
  `π₁ = Γ` is invariant while the component stays round, so the volume ratio `≈ vol(S³_{√6})/|Γ|` is
  preserved without accumulated loss. Then apply `κ₁` at radius `r₀` at that time. This needs
  history-level component tracking across surgeries, including components born by capping. It is
  research-level and I have no estimate.
- **(b) Consult** on how Perelman II 5.2 / KL §79 get small-scale noncollapsing inside ε-round
  components under the canonical-neighbourhood assumption, before committing to (a).

Rejected: a round-volume clause on C4, because of the constant order (C1s C2s before κ) and the
circularity in §1.1.

Until then, the honest skeleton is a separate sorry leaf that covers only `hhigh` for round witnesses.
It should have exactly the hypotheses of S7's `hhigh`, with the witness in hand, and it must not
assume the leaf's conclusion.

## 6. Addendum (review H1): round case closed under simple connectivity

This section supersedes §1.1 and §5 for the Poincaré endgame. Second probe: 9 declarations, **0 errors**,
only `sorry` warnings. It imports the leaf file, `…Topology.Ancestry`,
`…Extinction.Width.SurgeryWidthEvolution`, `…Topology.CanonicalNeighborhoodsThroughSurgeryStrong` and
`…CanonicalNeighborhood.RoundCanonicalWitness`. The class-to-component theorem R4 below compiled with a
real body; only its bridge R3 is `sorry`.

### 6.1 Literature split
Perelman discards near-round components at surgery; KL Remark 73.3 keeps them. Our leaf serves only the
simply connected endgame. Every component of every stage is then simply connected, and a round
component is `S³(√6)` up to scale, never a collapsed `S³/Γ`. The §1.1 counterexample (`S³/ℤₙ`) is
excluded by the class. It remains valid for non-simply-connected `P₀`, which this leaf no longer covers.

### 6.2 Interface change (exact places)
Supply: `rfs_simply_connected_history` (`Surgery/Topology/Ancestry.lean:17`), fed by
`Extinction.Width.initialIdentification_components_simplyConnected`
(`Extinction/Width/SurgeryWidthEvolution.lean:831`, namespace `…Extinction.Width`; precedent at
`Surgery/Topology/FiniteHorizonExtinction.lean:30`). The latter needs only
`[SimplyConnectedSpace P.Carrier]`, since `ConnectedSpace` is inferred.

To avoid an `unusedArguments` finding on Prop-valued `def`s (a `nolint` is forbidden), put the fact as a
**premise inside the body**, not as a `def` instance binder:
1. `SmallScaleNoncollapsingThroughSurgery P₀ g₀ : Prop := SimplyConnectedSpace P₀.Carrier → ∀ (B ε …)`.
   The probe elaborated this shape as `SimplyConnectedSpace P₀.Carrier → SmallScaleNoncollapsingThroughSurgery P₀ g₀`.
2. `NoncollapsingThroughSurgery P₀ g₀` (`CanonicalNeighborhoodInduction.lean:250`): same premise form.
3. `noncollapsingThroughSurgery_of_reducedVolume_of_smallScale`: `intro hsc`, then pass `hsc` to `hsmall`.
4. `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` (`CanonicalNeighborhoodsThroughSurgeryStrong.lean:272`)
   gains the theorem binder `[SimplyConnectedSpace P₀.Carrier]` and calls `hnon inferInstance`.
   `CanonicalNeighborhoodsThroughSurgeryStrong(At)` stays **unchanged**.
5. `hext_of_uniformDebitSurgeryStepStrong_of_canonicalNeighborhoodsStrong` (line 239) and
   `smoothPoincareConjecture_of_…` (line 254): change the binder to
   `hcn : ∀ (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric), CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀`.
   The probe elaborated this shape. `hext` already builds the instance before calling `hcn`, and
   `exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong` already has it.
6. `Skeleton/PoincareEndgame.lean`: the theorems `smallScaleNoncollapsingThroughSurgery`,
   `noncollapsingThroughSurgery` and `canonicalNeighborhoodsThroughSurgeryStrong` gain
   `[SimplyConnectedSpace P₀.Carrier]`. `smoothPoincareConjecture_holds` is unaffected.
   `UniformDebitSurgeryStepOfFactory.lean` only imports the file; it has no use site.

### 6.3 Round statements (all elaborate)
Namespace `…Perelman.CanonicalNeighborhood.FiniteHorn`. The variable block for R1 is
`{M} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]`.

**R0a (space-form rigidity; NOT in the tree).**
```lean
theorem exists_isometry_roundSphereThree_of_constantCurvature
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]
    [T2Space Z] [CompactSpace Z] [SimplyConnectedSpace Z]
    (h : SmoothRiemannianMetric I3 Z)
    (hcc : ∀ z (v w : TangentSpace I3 z),
      metricRm04At h z (fun i : Fin 4 => ![v, w, w, v] i) =
        (1 / 6 : ℝ) * (h.inner z v v * h.inner z w w - (h.inner z v w) ^ 2)) :
    ∃ Φ : Z ≃ₘ⟮I3, I3⟯ RoundSphereThree, ∀ z (v w : TangentSpace I3 z),
      roundSphereThreeMetric.inner (Φ z) (mfderiv I3 I3 Φ z v) (mfderiv I3 I3 Φ z w) =
        h.inner z v w
```
**R0b (volume of `S³(√6)`; NOT in the tree).**
```lean
theorem riemannianVolumeMeasure_roundSphereThree_univ :
    riemannianVolumeMeasure I3 RoundSphereThree roundSphereThreeMetric univ =
      ENNReal.ofReal (12 * Real.sqrt 6 * Real.pi ^ 2)
```
**R0 (corollary of R0a and R0b).**
```lean
theorem riemannianVolumeMeasure_univ_of_constantCurvature_of_simplyConnected
    {Z : Type u} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z] [IsManifold I3 ∞ Z]
    [T2Space Z] [CompactSpace Z] [SimplyConnectedSpace Z]
    (h : SmoothRiemannianMetric I3 Z)
    (hcc : ∀ z (v w : TangentSpace I3 z),
      metricRm04At h z (fun i : Fin 4 => ![v, w, w, v] i) =
        (1 / 6 : ℝ) * (h.inner z v v * h.inner z w w - (h.inner z v w) ^ 2)) :
    riemannianVolumeMeasure I3 Z h univ = ENNReal.ofReal (12 * Real.sqrt 6 * Real.pi ^ 2)
```
**R1 (the coordinator's statement, verbatim).**
```lean
theorem SpatialRoundComponent.volume_lower_of_simplyConnected
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M} {U : Set M}
    (D : SpatialRoundComponent g eps x U) [SimplyConnectedSpace U] :
    ENNReal.ofReal (6 * Real.sqrt 3 * Real.pi ^ 2 /
        (metricScalarAt g x * Real.sqrt (metricScalarAt g x))) ≤
      riemannianVolumeMeasure I3 M g U
```
Proof:
- `D.map` is a diffeomorphism `Z ≅ U` (`source_eq`, `target_eq`), so `Z` is simply connected and
  compact (`D.compact`). R0 then gives `vol_h Z = 12√6π²`.
- `metric_bounds` gives `Q·D.map*g ≥ ½h`, so `vol_g U ≥ (2Q)^{-3/2}·12√6π² = 6√3π²Q^{-3/2}`. The
  change of variables uses `PartialDiffeomorph` volume transport; `VolumeTransport` is in the tree.
- Arithmetic: `12√6/(2√2) = 6√3`.

**R2 (ball volume at the centre, round).** This is what S4 actually needs: a bound on a ball, not on `U`.
```lean
theorem exists_ball_volume_of_spatialRoundComponent (eps : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      {U : Set P.Carrier} (D : SpatialRoundComponent g eps x U), eps < 1 / 11 →
      SimplyConnectedSpace U → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r)
```
Proof:
- **Volume of `U`.** R1 gives `vol U ≥ 6√3π²Q^{-3/2}`.
- **Diameter.** `metric_bounds` gives `diam U ≤ √2·π√6·Q^{-1/2}`. `U` is a whole component, so
  `B(x,·) ⊆ U`. The in-tree lemmas are `metricDistance_le_of_roundComponent_diameterBound` and
  `roundComponent_edist_diameter_bound` (`RoundModelCoveringBall.lean:31,144`).
- **Curvature.** `|Rm| ≲ Q` on `U` comes from `comparison` (C^k-closeness to the constant-curvature `h`).
- **Radius.** `r ≤ 3Q^{-1/2}` follows from `scalar_abs_le_rm`.
- **Conclusion.** S3 from `r` up to `diam U` gives a universal κ.

**S4′ (S4 with `requiresVolume` replaced by simple connectivity of the component).**
```lean
theorem exists_ball_volume_of_spatialCanonicalWitness_of_simplyConnected (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      SimplyConnectedSpace (connectedComponent x) → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r)
```
Round case: `whole : U = connectedComponent x`, so rewrite and apply R2. The other three cases are S4.

**R3 (component bridge; namespace `…Surgery.Topology`).** Needed because `rfs_simply_connected_history`
speaks of `((H.stage j).component c).Carrier = componentOpen c`, not of `connectedComponent x`.
```lean
theorem OrientedThreeStage.simplyConnectedSpace_connectedComponent (P : OrientedThreeStage.{u})
    (x : P.Carrier) [SimplyConnectedSpace (P.component (ConnectedComponents.mk x)).Carrier] :
    SimplyConnectedSpace (connectedComponent x)
```
Proof: `{y | mk y = mk x} = connectedComponent x` (`ConnectedComponents.coe_eq_coe'`), then transport
through a homeomorphism.

**R4 (class supply; body compiled, apart from R3).**
```lean
theorem RetainedCoreHistory.simplyConnectedSpace_connectedComponent_stage
    {P₀ : OrientedThreeStage.{u}} [SimplyConnectedSpace P₀.Carrier] {g₀ : P₀.Metric}
    {B : ℝ} {p₀ : CutoffParameters} {δbound ρbound : ℝ} (H : RetainedCoreHistory P₀)
    (hH : H.InCutoffClass g₀ B p₀ δbound ρbound) (j : Fin (H.eventCount + 1))
    (x : (H.stage j).Carrier) : SimplyConnectedSpace (connectedComponent x) := by
  let h0 := Extinction.Width.initialIdentification_components_simplyConnected P₀ g₀ H.toHistory hH.1.some
  have := rfs_simply_connected_history H.toHistory h0 j (ConnectedComponents.mk x)
  exact (H.stage j).simplyConnectedSpace_connectedComponent x
```
The extended history `H.extendHorizon …` in the terminal half is in the class
(`hasCanonicalCutoffRecords_extendHorizon`), so R4 also applies there.

### 6.4 Rigidity: what the tree has (grep under `Geometry/` and `Topology/`)
Searched for `Killing`, `Hopf`, `spaceForm`/`space_form`, `ConstantCurvature`/`constant_curvature`,
`isometric_sphere`, `simply_connected_constant_curvature`, `Cartan`/`CartanAmbrose`/`developing`,
`Klingenberg` and the volume of a sphere.
- **No space-form rigidity, no Cartan–Ambrose–Hicks, no developing map, no Klingenberg, and no volume
  of `S³` exist.**
- What exists points the other way (model ⇒ quotient):
  - `roundSphereThreeMetric = 6·round` with `roundSphereThree_constant_curvature` (sec `1/6`,
    `RoundCanonicalWitness.lean:31,35`);
  - `RoundSphereQuotient`, `finite_deckGroup` and `nonempty_diffeomorph_sphereThree_sphereThree`
    (`PositiveDeckGroup.lean`);
  - `roundComponent_of_constantCurvature` and `exists_canonicalWitness_of_constantCurvature`
    (`RoundSpaceFormWitness.lean:114,176`);
  - conjugate-radius tooling in `Geometry/Comparison/Volume/BishopGromov.lean`.
- The Uhlenbeck and Hamilton "RoundLimit" files are flow statements, not rigidity.

R0a is therefore its own brick. Route (Cartan–Ambrose–Hicks, specialized):
1. Fix `z₀`. The map `F := exp_{z₀} ∘ ι ∘ exp_{N}⁻¹`, from `S³(√6)` minus the antipode, is a local
   isometry. This needs Jacobi fields for constant curvature; the conjugate radius is `π√6`.
2. Extend `F` over the antipode.
3. A local isometry from a compact space is a covering. `Z` is simply connected, so `F` is a
   diffeomorphism.

Estimate: 1500–3000 lines, depending on how much exponential-map and Jacobi-field API
`Geometry/Comparison` already exposes. R0b (volume of `S³(√6)` via `roundMetric` and a chart or
Fubini) is 150–300 lines.

Cheaper alternative, if only R0's `≥` is needed: `exp_{z₀}` restricted to `B(0, π√6)` is a local
isometry onto `Z`. Its lower Jacobian and surjectivity give `vol Z ≥ vol S³(√6)/deg`, and degree 1
still needs simple connectivity. So the saving is small; keep R0a.

### 6.5 Brick table, final (replaces §4's round row)

| # | Brick | Depends on | Lines |
|---|---|---|---|
| 1 | S3 local BG (+ `q = 0`) | CompactBall:162, Count:110 | 150–250 |
| 2 | S7 case assembly | S3 | 80–120 |
| 3 | S2a + S2 (+ last-stage twin) | window scalar bounds | 200–330 |
| 4 | S1 threshold-`M` dichotomy (+ twin) | BackwardTraceDistortion:642, Terminal:517 | 200–300 |
| 5 | S4 neck / positive / cap | BallVolume:150,286, S3 | 600–800 |
| 6a | R0b volume of `S³(√6)` | `roundMetric` | 150–300 |
| 6b | **R0a space-form rigidity** | exp map, Jacobi fields, covering | **1500–3000** |
| 6c | R0 → R1 → R2 → S4′ | 6a, 6b, S3, `VolumeTransport`, RoundModelCoveringBall | 250–400 |
| 7 | R3 + R4 component supply | Ancestry:17, SurgeryWidthEvolution:831 | 30–60 |
| 8 | S6 early layer | InitialSlab*:21,123 | 200–350 |
| 9 | S0 slice transfer | HistoryParabolicBall:860, ForwardTransfer:91,126 | 350–600 |
| 10 | Interface change §6.2 + leaf wiring | — | 330–500 |

Total: about 4000–7000 lines, of which R0a is 1500–3000. Rows 1–5 and 7–10 do not depend on R0a and
can proceed in parallel. With R0a left as a `sorry` brick, the leaf's round case is conditional on
exactly R0a.

### 6.6 Final statement list (every one elaborated)
- Probe 1: S0-def, S0, S1, S2, S3, S4, S6, S7.
- Probe 2: R0a, R0b, R0, R1, R2, S4′, R3, R4 (with R4's body), and the two interface shapes of §6.2
  (the premise form of the leaf; the `hcn` binder with `[SimplyConnectedSpace P₀.Carrier]`).
- In the leaf proof S4′ replaces S4. Its simple-connectivity input comes from R4 at `x : (H.stage j).Carrier`.
