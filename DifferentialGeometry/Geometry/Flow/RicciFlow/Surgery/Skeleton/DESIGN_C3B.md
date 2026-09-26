# C3b design: assembling `CapWindowContinuation` (2026-09-26)

This is a read-only design. No Lean file, git state or build was touched. Paths are relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/`. The statements below were **not** elaborated.
The scratch probe (outside the repo) stopped at import time because the shared `.lake` currently
lacks oleans (`…/NormalizedConeExclusion.olean` and `…/NormalizedBoundedCurvature.olean`, which a
running build is presumably rewriting). Re-probe the statements in §4 once the build finishes.
This design is coordinated with `DESIGN_28.md` (items ii and iv), which it relies on.

## 0. Failures first

1. **E3 and Lane T cannot be combined with the bridge as briefed.**
   `StrongNeck/LocalNeck/LocalCap/CanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn`
   all have the shape `∃ δ, …` *after* the source flow, point, time and witness are fixed. The δ
   comes from compactness on that particular source (`exists_rescaledMetric_comparison_tolerance_on_compact`).
   The bridge `exists_standard_comparison_of_cap_window_trace`, however, needs its accuracy `ε`
   before `H`, while `Q`, `T` and the point all depend on `H`. So one needs a tolerance that is
   uniform over all standard solutions `Q`, all times `T ≤ Θ` and all points `‖x‖ < Dcap+1`.
   Getting that requires (a) compactness of the standard-solution family and (b) stability of the
   witness when the point and time move. The library has (b) only for `WindowedModelWitness`
   (`WitnessStrictStability.lean`), not for `CanonicalWitness`. A field-by-field transport of
   `CanonicalWitness` (volume, gradient, time_derivative, scalar_bounds, rm_bound, radius/domain,
   each still to write) would therefore also need an openness theory that does not exist.
   **Recommendation:** go through `WindowedModelWitness`/`OrientedWitness` (route W, §1) and apply
   the uniform pipeline `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts` directly
   on `Gk.flow`. That single call yields every `CanonicalWitness` field together with
   `capTubeHasNeckChart`, so E3/Lane T are not needed for C3b at all.
2. **D2 cannot supply the derivative and gradient clauses as stated.** Its constant
   `C' = C'(Θ)` needs `θcap ≤ Θ`, but in `CapWindowContinuation` the value `θcap` is quantified
   *after* `Ctime₀ Cgrad₀` (and in the assembly it comes from Crossing, after κ). `C'(Θ)` blows up
   as `Θ → 1`. The repair (§1 step 5) splits into two cases. In the standard-aged case, use the
   absolute constant of `exists_windowedModelWitness_scalar_derivative_bounds`. In the young case,
   `T ≤ Θ₂(τQ) < 1` holds automatically, and D2 is used only at `Θ₂`. D2 also needs a quantifier
   swap, `∀ Θ, ∃ c C', ∀ C, ∃ Cbirth, …` (its log says `C'` depends only on Θ). As stated today,
   `C'` comes after the derivative constant `C`, and `C` must be `2·Ctime`, which is universal.
3. **The bridge hypothesis `Gk.DerivativeBoundBefore C qcan t` at the current time.** The leaf only
   knows `…Before t₀`, and the bridge quantifies over *all* points of the carrier on
   `(time k, t)`. Localizing it to the cap region does not help: the bridge needs the bound on the
   `Dbig` window but concludes only on `D < Dbig`, so the region would never close up. Fix:
   - (a) If `t₀ > time k`, call the bridge with `(C, q) := (2·Ctime, 2·qcan)`. Prove
     `Gk.DerivativeBoundBefore (2Ctime) (2qcan) t` for `t < t₀ + η` by uniform continuity of
     `∂ₜR` on `carrier × [t₀ − η', t₀ + η]`, with `η` depending on `G`, which the leaf allows.
   - (b) If `t₀ = time k`, no earlier interval exists inside `Gk`. A *slab-start slice* bound on
     `∂⁺R(time k)` is needed: the left limit on the retained region, and the standard-cap
     computation `≤ C_std/c²·R²` on fresh caps. This is the pre-existing boundary-slice issue
     (`DESIGN_28.md` failure 6). It is **open**; the statement is in §4, L10b.
4. **No false configuration from the backward window.** On `Gk`, the witness window is
   `[t − (δR)⁻¹, t]`. Since `τmin ≤ R(t − time k)` and `δ⁻¹ ≤ τ₀ ≤ τmin`, it lies in
   `[time k, t]`. It never reaches the birth time `time j.succ`, not even when `j.succ < k`. On `S`,
   the window lies in `[T_k, T]` with `T_k = q(time k − time j.succ)`, because
   `R_S(T − T_k) = R(t − time k)`. The `StrongNeck` windows inside the pipeline's witness are
   placed by the pipeline itself, under `Ioo (t − (δR)⁻¹) t ⊆ regular`. If `θcap ≤ 0`, then
   `CapWindowPoint` is empty (`t − time j.succ > 0`). Use `Θ := max θcap (1/2)` for the bridge's
   `0 < Θ`.
5. **Orientation.** `OrientedWitness` is needed on `Gk` with `(H.stage k).orientation`. The
   window's orientation is its pullback, which is `±` the standard one because the window is
   connected. No pullback of `TangentOrientationSection` along a local diffeomorphism was found; see
   brick L7b.

## 1. Route W: assembly at a cap-window point

Setting: we are in the event branch (`k = j.castSucc`, `a = time k`) or the terminal branch
(`k = last`). We have `(y,t)` with `CapWindowPoint records k y t Dcap θcap`, `t₀ ≤ t < t₀ + η` and
`qcan < R := Gk.flow.scalar t y`. Unpack the point as `(j, hl, A, b, x)`. Set
`q := ((records j).static b).neck.scale` and `T := q(t − time j.succ) ≤ θcap`.

1. **Bridge** (`Topology/CapWindowStandardComparison.lean`,
   `exists_standard_comparison_of_cap_window_trace`). Call it with `Θ := max θcap (1/2)`,
   `C := 2·Ctime`, `D := D_W`, `ε := e_W`, `N := N_W` (the last three from L6 at `(Θ, r := Dcap+1)`),
   and `qcan := 2·qcan`. The class inputs come from `DESIGN_28` (iv):
   `ρmax ≤ √(Cbirth/(4qcan))` and `≤ √(a₀/2)`, with `a₀` from
   `exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀`
   (`Topology/HamiltonIveyPinching.lean`), which also supplies the two initial-data hypotheses.
   `DerivativeBoundBefore` comes from Failure 3. The bridge returns `Ξ`, `gflow`, the window flow
   `S` on `closed 0 T` (`IsSolutionOn`), `S τ = Ξ^*(q·gflow(time j.succ + τ/q))`,
   `gflow = backwardSurvivorIncomingMetric` on `[time k, t]`, a standard solution `Q`, and
   `metricDerivNorm i (S τ) (Q τ) < e_W` for `i ≤ N_W` and `τ ∈ [0, T]`. Let `z := ⟨x.val, _⟩`,
   so that `(Ξ z).val.val = y` and `R_S(z,T) = q⁻¹R`.
2. **Age.** `T·R_S(z,T) ≥ (T − T_k)R_S(z,T) = R(t − time k) ≥ τmin ≥ τ₀ ≥ τQ`.
3. **Witness on S.** L6 gives `OrientedWitness S o_W δ standardModelKappa z T`, where `δ` is the
   pipeline tolerance of §3. Inside L6, the standard solution's windowed witness comes from
   `exists_standard_high_scalar_model_threshold` (`StandardSolution/HighCurvatureModels.lean:126`).
   Its requirement `τ ≤ T`, `Q₀ ≤ R_Q` is derived from `τQ ≤ T·R` as in
   `CanonicalWitnessPositiveAge.lean:66`. Its backward window lies in `Q`'s domain `[0, ·)`, so it
   sits inside the bridge window `[0, T]` automatically.
4. **S → Gk, exact and with no tolerance loss.** First restrict `S` to `[T_k, T]`
   (`orientedWitness_timeRestrict`; the window fits by step 2). Then shift by `T_k`
   (`orientedWitness_paraSolution_iff` with `A = 1`, `SelectedCountersequenceAdapter.lean:231`). On
   that interval, `S(T_k + σ) = Φ^*(parabolicSolution Gk (time k) q)(σ)` with
   `Φ v := (Ξ v).val.val`. Push forward along `Φ` (L7), then undo the parabolic rescaling
   (`orientedWitness_paraSolution_iff`). The result is `OrientedWitness Gk.flow o_k δ κ y t`, and
   `Ioo (t − (δR)⁻¹) t ⊆ Ioo (time k) s` holds because `τ₀ ≥ δ⁻¹`.
5. **Canonical witness.** Apply `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts
   (alpha := ε) (H := 1)` (`CanonicalNeighborhood/WindowedBufferedCanonical.lean:20`) on `Gk.flow`.
   Then `B.canonicalWitness_mono B.tolerance_lt.le`, `hB.mono_eps`, and `enlarge_constants`
   (`CanonicalStrictBounds.lean:141`, `CanonicalCapCollar.lean:26`) give
   `∃ W : CanonicalWitness Gk.flow ε C1 C2 y t, W.capTubeHasNeckChart ε`.
6. **Derivative and gradient clauses** hold at every cap-window point with `R > qcan`, with or
   without the age condition:
   - *Case A* (`τQ ≤ T·R_S(z,T)`): L6 gives a windowed witness on `S`, and
     `exists_windowedModelWitness_scalar_derivative_bounds`
     (`CanonicalNeighborhood/WindowedGoodPointBounds.lean:237`, absolute `C_W`) bounds `∂R_S` and
     `dR_S` at `T`. L8 moves them to `Gk` at `(y,t)`: the left germ of `S` on `[T_k, T]` is the
     scaled pullback of `Gk`, `∂ₜR_G = q²∂_τR_S`, and `R_G = qR_S` (scale-invariant).
   - *Case B* (`T·R_S < τQ`): L9 gives `T ≤ Θ₂ := (τQ+1)/(τQ+1+c₀)`, with `c₀` from
     `exists_standard_scalar_lower_bound` (`StandardSolution/StandardTerminalBlowup.lean:61`) and
     `|R_S − R_Q| < 1`. Then D2 at `Θ₂` (`Topology/CapWindowDerivativeBounds.lean`,
     `exists_derivative_gradient_bounds_of_cap_window_trace`, after the quantifier swap) gives the
     bounds with `C'(Θ₂)`.

## 2. Leaf hypotheses → bridge class gaps

| Bridge/D2 hypothesis | Discharge |
|---|---|
| `IsCanonicalCutoffRecordFamily`, `δbound ≤ δ₀`, `R ≤ p₀.modelRadius`, `m₀ ≤ modelOrder`, `modelAccuracy ≤ ζ₀` | Direct, with `Rcap := max R R₂`, `mcap := max m₀ m₂`, `εcap := min ζ₀ ζ₂`, `δmax := min δ₀ δ₂` |
| `qcan ≤ Cbirth·scale` (with `qcan := 2qcan`) | `DESIGN_28` (ii)+(iv): `ρmax` chosen after `qcan`, `ρmax ≤ √(Cbirth/(4qcan))` for both bridge instances; `inv_two_mul_sq_lt_static_scale` |
| `1 ≤ a₀·scale`, Hamilton–Ivey and `−3/a₀ ≤ R` on `g₀` | `a₀` from `exists_pos_fixedHamiltonIveyRegion_for_identified_histories`, `ρmax ≤ √(a₀/2)` |
| `H.EventSlabsDerivative (2Ctime) (2qcan) k` | Monotonicity from the leaf's `EventSlabsDerivative Ctime qcan k` |
| `Gk.DerivativeBoundBefore (2Ctime) (2qcan) t` | L10a (`t₀ > time k`); **L10b open** (`t₀ = time k`) |
| `Gk.flow.base.metric (time k) = H.initialMetric k` | Incoming-slab initial condition (event: `…incoming` initial lemma; terminal: `IsContinuationSlab`) |
| `θcap ≤ Θ`, `0 < Θ < 1` | `Θ := max θcap (1/2)` |

## 3. Constants and accuracy bookkeeping

- The leaf's `ε` is the pipeline `alpha`. Obtain `(Cε, δ0)` from
  `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts hε hε' 1`, and set
  `δ := min δ0 (1/4)`. Every step from `S` to `Gk` is exact, with no loss.
- Inside L6, apply the standard threshold at `δ/4`. `mono` to `δ/2` makes the witness *strict*
  (L2), and the perturbation L4 loses at most `δ/2`. `e_W` and `N_W` are L6 outputs. E3's `2α`
  plays no role.
- `C1₀ = C2₀ := Cε`.
  `τ₀ := max τQ δ⁻¹ + 1`.
  `Ctime₀ := max C_W C'(Θ₂)`.
  `Cgrad₀ := max (2C_W) C'(Θ₂)`.
  All four depend on `ε` only, as the quantifier order requires. `τQ` depends on `δ` only.
  `Θ₂` depends on `τQ` and `c₀`.
- After `θcap`: fix `Θ` and `(D_W, N_W, e_W)`, the bridge `(R, m₀, ζ₀, δ₀)`, and D2 at `Θ₂`
  `(R₂, m₂, ζ₂, δ₂)`. Choose `ρmax` after `qcan` (`DESIGN_28` ii), and `η` after `G` (L10).

## 4. Missing lemmas (unchecked statements)

- **L1** (standard-solution compactness; `StandardSolution/…`). Its body is one application of
  `exists_standard_solution_limit_of_initial_convergence_on_open_cover` (`InitialMetricLimit.lean:14`)
  with `S n i := (Q i)` restricted to `standardCapWindow n` on `closed 0 ((Θ+1)/2)`. Curvature
  bounds come from `standard_metric_bounds_on_shorter_windows`.
  ```lean
  theorem StandardSolution.exists_subseq_tendsto (Θ : ℝ) (hΘ : 0 ≤ Θ) (hΘ1 : Θ < 1)
      (Q : ℕ → StandardSolution) :
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ Q' : StandardSolution, ∀ n : ℕ,
        ∀ K : Set (standardCapWindow n), IsCompact K → ∀ p : ℕ, ∀ e : ℝ, 0 < e →
        ∃ j, ∀ i ≥ j, ∀ t ∈ Icc 0 Θ,
          metricDerivNormSupOn K p (((Q (ρ i)).val.metric t).restrictOpen _)
            ((Q'.val.metric t).restrictOpen _) (StandardCap.metric.restrictOpen _) < e
  ```
- **L2** `WindowedModelWitness.monoEps` (`eps' ≤ eps`, needs `IsSolutionOn` and a regular window
  for `restrictTimes`), plus a strictness corollary when `eps' < eps`. Nothing like this exists
  (only `mono_kappa` and `mono_of_(interior_)regular`).
- **L3** `WindowedModelWitness.toRestrictOpen`: from the ambient manifold to an open `U` containing
  `W.embedding '' closedBall(modelRadius eps + 1)`. This is the converse of `ofRestrictOpen`, which
  requires `IsClosed U`. The easy direction holds because intrinsic `U`-balls lie inside ambient
  balls.
- **L4** (the core; it generalizes `WindowedModelWitness.eventually_strict_of_regular_window`,
  `WitnessStrictStability.lean:33`, from one flow to a convergent sequence):
  ```lean
  theorem WindowedModelWitness.eventually_of_tendsto_flows
      {D : RealTimeInterval} {S₀ : SolutionOn (I := I3) (M := M) D} (hS₀ : IsSolutionOn S₀)
      {S : ℕ → SolutionOn (I := I3) (M := M) D} (hS : ∀ n, IsSolutionOn (S n))
      {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S₀ x t)
      (hwindow : Icc (t - (eps * S₀.scalar t x)⁻¹) t ⊆ D.regular)
      (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
          tensor02CovDerivNormWith a (W.comparison.jet b s)
            (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps)
      (hconv : ∀ p : ℕ, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ τ ∈ D.carrier, ∀ i ≤ p, ∀ v : M,
        metricDerivNorm i ((S n).base.metric τ) (S₀.base.metric τ) Rref v < e)
      {x' : ℕ → M} (hx' : Tendsto x' atTop (𝓝 x)) :
      ∀ᶠ n in atTop, Icc (t - (eps * (S n).scalar t (x' n))⁻¹) t ⊆ D.regular ∧
        Nonempty (WindowedModelWitness eps kappa (S n) (x' n) t)
  ```
  plus the `OrientedWitness` form. Space–time jets come from `SpatialClosenessTimeJets.lean:53`
  (fixed `S₀`, which is allowed inside a contradiction). Composition uses
  `MetricComparisonOn.exists_trans_on_compact` (`LocalComparisonComposition.lean:29`). The change
  of scale `R_{S n}(x' n)` versus `R_{S₀}(x)` reuses the recentering of
  `WitnessOpennessPreparation.lean` (`eventually_admissible_recentering`).
- **L5** (time shift and convergence). For `S'ₙ(σ) := Sₙ(σ + Tₙ − T∞)` on the fixed window `D'`
  and the interval `[a, T∞]`: the spatial closeness `S'ₙ → Q∞` follows from bridge closeness,
  L1, `metricDerivNorm_triangle`, and uniform time continuity of `Q∞`'s spatial jets on
  `closure D' × [0, Θ']`.
- **L6** (uniform standard-close witness; the probe statement):
  ```lean
  theorem exists_uniform_orientedWitness_of_standard_close {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
      ∃ τQ : ℝ, 0 < τQ ∧ ∀ (Θ r : ℝ), 0 < Θ → Θ < 1 → 0 < r →
      ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
      ∀ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ →
      ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0 T hT)), IsSolutionOn S →
      (∀ τ ∈ Icc 0 T, ∀ i ≤ N, ∀ v : standardCapWindow D,
        metricDerivNorm i (S.base.metric τ)
          ((Q.val.metric τ).restrictOpen (standardCapWindow D))
          (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
      ∀ (o : TangentOrientationSection (standardCapWindow D)) (z : standardCapWindow D),
        ‖z.val‖ < r → τQ ≤ T * S.scalar T z →
        OrientedWitness S o δ standardModelKappa z T
  ```
  Proof by contradiction over `(Dₙ → ∞, Nₙ → ∞, eₙ → 0, Qₙ, Tₙ, Sₙ, zₙ, oₙ)`:
  - L1 gives `Q∞`. Pass to subsequences with `Tₙ → T∞ > 0`, `zₙ → z∞`, and a constant sign of `oₙ`.
  - `T∞ > 0`, because `T·R ≥ τQ` and `R ≤ K(Θ)`.
  - `Q∞` has a strict witness at `(z∞, T∞)` (threshold at `δ/4` plus L2). Restrict it to `D'` (L3).
  - L5, then L4 at the points `(zₙ, T∞)`, then shift back. Contradiction.
- **L7** (pushforward along a flow isometry; exact):
  ```lean
  theorem OrientedWitness.map_of_localPull {N : Type u} [...] {DN DM : RealTimeInterval}
      (S : SolutionOn (I := I3) (M := N) DN) (S' : SolutionOn (I := I3) (M := M) DM)
      (Φ : PartialDiffeomorph I3 I3 N M ∞) (hΦ : Φ.source = univ) (o : TangentOrientationSection M)
      {eps kappa : ℝ} {x : N} {t : ℝ} (ht : t ∈ DM.carrier)
      (hwin : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ DM.carrier)
      (hmetric : ∀ τ ∈ Icc (t - (eps * S.scalar t x)⁻¹) t,
        S.base.metric τ = localPullMetric (S'.base.metric τ) Φ (Φ.isLocalDiffeomorph …)) :
      OrientedWitness S (o.pullback Φ) eps kappa x t → OrientedWitness S' o eps kappa (Φ x) t
  ```
  Care points:
  - Redefine `pullback` and `jet 0` for all `s`, keeping `jet (b+1)`: `derivWithin` over the
    window reads only window values.
  - `source_capture` follows from `riemannianBallOf_subset_image_of_metric_lower`
    (`Geometry/Metric/Comparison/IntrinsicBallImage.lean:14`) with `C = 1`, together with compactness
    of the closed `S`-ball, which comes from `buffered_ball` and the `(1 ± eps)` equivalence.
  - **L7a**: build `Φ := (Ξ ·).val.val` as a `PartialDiffeomorph` from `IsSmoothEmbedding` and an
    open image. No such constructor was found.
  - **L7b**: `TangentOrientationSection.pullback` along a local diffeomorphism, plus the fact that
    on a connected open subset of `E3` it is `±` the standard section. Neither was found.
  - Also check that `L.extendedMetric τ` is the restriction of `Gk.flow.base.metric τ` for
    `τ ∈ [time k, t)`.
- **L8** transfers the derivative and gradient bounds from `S` at `T` to `Gk` at `t`. Ingredients:
  the scalar and differential scaling already used by D2
  (`metricScalarAt_localPullMetric_scaleMetric`), and left-germ congruence of `derivWithin (Iic ·)`
  (`Filter.EventuallyEq.derivWithin_eq`).
- **L9** proves `T·R_S < τQ ∧ |R_S − R_Q| < 1 ∧ T ≤ Θ ⇒ T ≤ (τQ+1)/(τQ+1+c₀)`.
- **L10a** (continuity; in the slab file):
  ```lean
  theorem IncomingSlab.exists_derivativeBoundBefore_two_mul_of_before {P : OrientedThreeStage}
      {a s : ℝ} (G : P.IncomingSlab a s) {C : ℝ≥0} {q t₀ : ℝ} (hq : 0 < q) (ht₀ : a < t₀) (hts : t₀ < s)
      (h : G.DerivativeBoundBefore C q t₀) :
      ∃ η, 0 < η ∧ ∀ t, t < t₀ + η → G.DerivativeBoundBefore (2 * C) (2 * q) t
  ```
- **L10b** (slab-start slice; **open, needs a lead decision**): prove it at `time k`, handling the
  retained region by the left limit and fresh caps by the standard-cap evolution formula. The
  alternative is to change the leaf interface to `t₀ ∈ Ioo` and provide the start separately.
  Either way it is shared with Crossing/X1 and with `DESIGN_28` failure 6.

## 5. Bricks in dependency order (line estimates)

| # | Brick | Lines |
|---|---|---|
| 0 | D2 quantifier swap (`C'` before `C`); leaf edits from `DESIGN_28` (ii)+(iv) | 20 + (DESIGN_28) |
| 1 | L1 standard compactness | 150–250 |
| 2 | L2 `monoEps` + strictness | 80–150 |
| 3 | L3 `toRestrictOpen` | 100–150 |
| 4 | L4 perturbation (sequence form; the riskiest brick) | 400–700 |
| 5 | L5 time shift and convergence | 150–250 |
| 6 | L6 contradiction assembly | 300–450 |
| 7 | L7 + L7a + L7b pushforward, embedding, orientation | 250–400 |
| 8 | L8 + L9 | 150–250 |
| 9 | L10a | 100–200 |
| 10 | L10b (open; decide first) | 300–600 |
| 11 | Leaf assembly (both branches, cases A/B, constants of §3) | 300–450 |

Total ≈ 2.3k–3.8k lines. Bricks 1–3, 7, 8 and 9 are independent and can run in parallel. 4 needs 2.
6 needs 1–5. 11 needs everything, and 10 needs the lead's decision.
