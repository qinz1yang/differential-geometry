# Design: B6d history glue (F2 containment and the time-0 slice), 2026-09-26

Read-only design on `codex/pc-target-c-psf` @ 9126abc30 plus uncommitted lanes. Paths are relative to
`DifferentialGeometry/Geometry/Flow/RicciFlow/`. Every statement below was elaborated with `sorry`
bodies, outside the repo, with `LEAN_NUM_THREADS=2`. The uncommitted
`Surgery/Topology/AncientPointedFlowLimitTransfer.lean` and `TracedRegionAncientLimitWitnesses.lean`
were compiled as scratch modules for this: Transfer 71 s, no output; Witnesses, no output. Each probe
produced only `declaration uses sorry`. The probes have since been removed.

## 0. Failures first

**F-a. FALSE: `hEreg` at `s = 0`, and `(E n).Finite`.** For every `n`, the time-0 slice is
exceptional, whether or not `tₙ = t₀ₙ`. `CrossingContinuation`
(`Surgery/Topology/CanonicalNeighborhoodContinuationLeaves.lean:232`) supplies
`SpatiallyCanonicalBefore … t₀`, `DerivativeBoundBefore … t₀` and `CanonicalBefore … t₀`, and all
three are on the open interval `(a, t₀)`. The bad point satisfies `tₙ ∈ [t₀ₙ, t₀ₙ + ηₙ)`.
- The whole normalized sliver `[−Rₙ(tₙ − t₀ₙ), 0]` therefore has no witness and no derivative bound.
  The bad point may be exactly the one that violates the derivative clause.
- So `E n` is not finite. It is a finite set of normalized stage starts together with that interval.
- B6B3's "E n = stage starts" and the current headline's `(∀ n, (E n).Finite) → (∀ s ≤ 0, ∀ᶠ n, s ∉ E n)`
  are both unsatisfiable for the Crossing sequence.

**F-b. FALSE: `hEreg` for `s < 0` as well.** Configuration: the current slab start `aₙ` (an event
time) sits at `Rₙ(tₙ − aₙ) = c` for every `n`, with `c ∈ (0, θ)` fixed.
- The young-point selector only gives `Rₙ(tₙ − aₙ) < θ`, and nothing else constrains `c`.
- Then `−c ∈ E n` for all `n`, and a subsequence does not help.
- Earlier events can pin other normalized times in the same way.
- Repair: no `hEreg` at all. Transfer at shifted approximant times instead (§2).

**F-c. Proposal (2)(b) (add `SpatiallyCanonicalOn` to `CrossingContinuation`) is circular and
unnecessary.**
- C3's output on `[t₀, t₀ + η)` is what the Crossing leaf is proving.
- C4 is proved from C3, so C4's output cannot feed it either.
- The age-restricted `CanonicalBoundsOn` witness clause is vacuous for these young points (review G
  item 6).
- No interface change is needed. The time-0 slice is handled by the approximant time shift and the
  sliver `Rₙ(tₙ − t₀ₙ) → 0` (§2).

**F-d. Correction to the B6D log.** The log says `IsSolutionOn` gives no `C^p` time continuity. That is
wrong at interior regular times:
- `MetricFamilySmoothOn.frameCompSmooth` gives joint smoothness on `D.regular ×ˢ u`.
- `chartGram_smooth_of_solution` (`Extension/Restart/SolutionBounds.lean:303`),
  `chartGramOnE_jointContDiffOn` (`Extension/Regularity.lean:504`) and
  `metricDerivNorm_tendstoUniformlyOn` (`Geometry/Metric/Convergence/Metric/Parameter.lean:115`) then
  give it.

Continuity is genuinely missing only at the closed end `0` of the limit. The route in §2 needs no
limit-level time continuity. It uses a uniform-in-`n` time-Lipschitz bound of the approximants.
- That bound is provable because slabs carry `MetricSmoothUpTo`, a smooth extension across closed
  ends (`Surgery/Topology/EventData.lean:183`).
- It also needs the Shi jets of the traced region.

**F-e. FALSE as sketched: F2 with the two-sided `|Rm| ≤ K(k)` bound.**
- `metric_inner_exp_bounds_of_curvature_bound` gives `h(0) ≤ exp(18√K(k)(k+1))·h(s)`. That factor
  depends on `k`, so `qW` would depend on `k`.
- B6d's `qW` must be one constant: the limit threshold `4·max qW 1` feeds a single per-slice lemma.
- Fix: use the rescaled pinching. For each `k`, eventually `Ric(h k n s) ≥ −δ` with `δ(k+1) ≤ 1`, so
  `h(0) ≤ e²·h(s)` uniformly. The smallness of the pinching needs a scalar bound on `W k n`, which
  B6b′ does not export today (export (vii) below).

**F-f. Gap in B6B3 lemmas 3 and 4.**
- Lemma 4's `hcurrent : DerivativeBoundBefore … t` at the base `t = tₙ` is not available. The leaf
  gives it only up to `t₀ₙ`.
- Lemma 3's `hstage` quantifies over `v < t`.
- Both must take a cutoff `t₀` (`v < t₀`); see B12.

**F-g. Flag for the B3F lane and the lead.** DESIGN_MAXWINDOW §3.2b applies B3e "at `tₙ`" with the
hypothesis `∀ x, q < R → witness` on the slice `tₙ`. That is unavailable for the same reason as F-a.
- It is not repaired by the §2 device: B3e outputs a ball bound, not an alternative.
- B1's sliver lemma (`Surgery/Topology/SliverForwardComparison.lean:262`) is whole-slice `C⁰` only.
  Its bound `2K` is the unnormalized slice sup, so it gives no local `Q·Rₙ` bound across the sliver.

**F-h. Junk `sSup` values.** `metricDerivNormSupOn` is an `sSup` and equals 0 on unbounded sets. The
new Lipschitz input is therefore stated pointwise with `metricDerivNorm`.

The case `t₀ₙ = aₙ = 0` has no earlier good times. It is excluded eventually by M7(c): `Rₙtₙ → ∞`
together with `Rₙ(tₙ − t₀ₙ) → 0`.

## 1. Answers to the brief

- **(1) F2 containment.** The alternative's window is a neck at `f z`, or a neck at `w` with
  `d(fz, w) < C/√R`. Its extent in the normalized stage metric at time `v` is at most
  `(C + (D + 2ε⁻¹)√C)/√R(z)`, with `D` from `exists_spatialNeck_window_edist_le` (Transfer:776).
  - Cross-model capture (`ball_subset_image_of_metric_lower_crossModel`,
    `Perelman/CanonicalNeighborhood/CrossModelBallCapture.lean:21`) has two inputs: source
    `(W, h(0))`, the closed ball of radius `1` around `z`, which is compact inside the `(k+2)`-ball
    ⊆ `W`; and the lower bound `h(0) ≤ L²·h(s)` with `L = e`.
  - It places the stage ball of radius `1/e` inside `range f_j`.
  - Hence `qW := max Cs (e·(C + (D + 2ε⁻¹)√C))²` with `C := max (2|C1|) C2`. This is the "`qW ≥ E²`"
    of the brief, with `E` explicit and `k`-free.
- **(2) Time-0 slice.**
  - (a) is false (F-a).
  - (b) is not available (F-c).
  - Continuity of `R(G t)` alone cannot give the bound at `0`: the B6D log's `β ~ 1/|s|` objection
    stands.
  - Resolution: continuity of the METRIC, at the approximant level. Pick `σₙ ↑ s` outside `E n`,
    which is possible for every `s ≤ 0` because `E n \ [−ζₙ, 0]` is finite and `ζₙ → 0`. Then
    ```
    ‖φ*h(σₙ) − G(s)‖_{C^p(K)} ≤ ‖φ*h(σₙ) − φ*h(s)‖ + ‖φ*h(s) − G(s)‖
                              ≤ L_k|σₙ − s| + o(1)
    ```
    The first term is the time-Lipschitz export; the second is B6a's convergence, which is uniform
    in `t`.
  - B6d's single-index transfer then runs verbatim with `h(σₙ)` in place of `h(s)`.
  - This covers `s = 0`, the event times of F-b, and every other `s`. No history datum at `tₙ` is
    used, and `hEreg` disappears.

## 2. Exact statements (all elaborate)

Namespace `…Perelman.CanonicalNeighborhood.FiniteHorn` unless noted; `universe v`/`w` as in Transfer.

**B1** (the time selector; about 60–100 lines, generic, `Order/Filter`-level):
```lean
theorem exists_tendsto_forall_not_mem_of_finite_diff_Icc {E : ℕ → Set ℝ} {ζ : ℕ → ℝ}
    (hζ : Tendsto ζ atTop (𝓝 0)) (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite) {s : ℝ}
    (hs : s ≤ 0) :
    ∃ σ : ℕ → ℝ, Tendsto σ atTop (𝓝 s) ∧ ∀ n, σ n ≤ s ∧ σ n ∉ E n
```

**B2** (Grönwall for `Ric ≥ −δ`; about 80–150 lines, home `Estimates/`, template
`Perelman/KappaSolutions/KLimMetricTimeControl.lean:27`; namespace `DifferentialGeometry.PDE.RicciFlow`,
generic `E H I M` with `[CompleteSpace E] [T2Space M]`):
```lean
theorem metric_inner_le_exp_mul_of_ricci_lower_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) {a b δ : ℝ} (hab : a ≤ b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (x : M)
    (u : TangentSpace I x)
    (hRic : ∀ q ∈ Ioo a b, -δ * (S.base.metric q).inner x u u ≤ S.ricciAt q x (vec2 u u)) :
    (S.base.metric b).inner x u u ≤ Real.exp (2 * δ * (b - a)) * (S.base.metric a).inner x u u
```

**B3** (pinching to Ricci; 100–240 lines):
- The first theorem is the manifold form of `RicciRayleighOperator.lean:217`, via
  `curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le`
  (`Curvature/DimensionThree/CurvatureOperator/LeastEigenvalue.lean:1153`).
- The second is from `exists_forall_rescalePinchingFunction_le` (`PinchingDatum.lean:139`) plus
  monotonicity.
```lean
theorem neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt {M : Type*}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) (x : M) {δ : ℝ}
    (h : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ)
    (u : TangentSpace I3 x) :
    -(2 * δ) * g.inner x u u ≤ metricRicciAt g x (vec2 u u)

theorem exists_forall_rescalePinchingFunction_le_of_tendsto {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop)
    (B δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ B → rescalePinchingFunction (Q n) Phi u ≤ δ
```

**B4** (lifting short paths to the pulled-back metric; 150–300 lines. It is the path-lifting core of
`PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower`; reuse it):
```lean
theorem riemannianEDistOf_localPull_lt_of_ball_subset_range {M N : Type v}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I3 M) {f : N → M} (hf : IsLocalDiffeomorph I3 I3 ∞ f)
    (hinj : Injective f) (z : N) {ρ : ℝ} (hball : riemannianBallOf g (f z) ρ ⊆ range f)
    {p : M} (hp : riemannianEDistOf g (f z) p < ENNReal.ofReal ρ) :
    ∃ w : N, f w = p ∧ riemannianEDistOf (localPullMetric g f hf) z w =
      riemannianEDistOf g (f z) p
```

**B5** (F2 core; 150–250 lines):
- Capture: `ball_subset_image_of_metric_lower_crossModel`.
- Necks are pulled back by `SpatialNeck.pushforward` along `Φ.symm`, as in Transfer:725.
- The component clause passes through the continuous image.
- Distances are handled by B4.
- `D` comes from `exists_spatialNeck_window_edist_le`.
```lean
theorem exists_neckAlternatives_localPull_of_metric_lower :
    ∃ D : ℝ, 0 < D ∧ ∀ {M N : Type v} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [TopologicalSpace N]
      [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]
      (g : SmoothRiemannianMetric I3 M) (h0 : SmoothRiemannianMetric I3 N) {f : N → M}
      (hf : IsLocalDiffeomorph I3 I3 ∞ f), Injective f → ∀ (z : N) {r L eps C : ℝ},
      0 < r → 0 < L → 1 ≤ C → IsCompact (riemannianClosedBallOf h0 z r) →
      (∀ y ∈ riemannianClosedBallOf h0 z r, ∀ u : TangentSpace I3 y,
        h0.inner y u u ≤ L ^ 2 * (localPullMetric g f hf).inner y u u) →
      0 < metricScalarAt g (f z) →
      L * (C + (D + 2 * eps⁻¹) * Real.sqrt C) < r * Real.sqrt (metricScalarAt g (f z)) →
      (Nonempty (SpatialNeck g eps (f z)) ∨
        (∃ w : M, Nonempty (SpatialNeck g eps w) ∧
          metricScalarAt g (f z) ≤ C * metricScalarAt g w ∧
          metricScalarAt g w ≤ C * metricScalarAt g (f z) ∧
          riemannianEDistOf g (f z) w < ENNReal.ofReal (C / Real.sqrt (metricScalarAt g (f z)))) ∨
        ∀ y ∈ connectedComponent (f z), metricScalarAt g y ≤ C * metricScalarAt g (f z)) →
      Nonempty (SpatialNeck (localPullMetric g f hf) eps z) ∨
        (∃ w : N, Nonempty (SpatialNeck (localPullMetric g f hf) eps w) ∧
          metricScalarAt (localPullMetric g f hf) z ≤
            C * metricScalarAt (localPullMetric g f hf) w ∧
          metricScalarAt (localPullMetric g f hf) w ≤
            C * metricScalarAt (localPullMetric g f hf) z ∧
          riemannianEDistOf (localPullMetric g f hf) z w <
            ENNReal.ofReal (C / Real.sqrt (metricScalarAt (localPullMetric g f hf) z))) ∨
        ∀ y ∈ connectedComponent z, metricScalarAt (localPullMetric g f hf) y ≤
          C * metricScalarAt (localPullMetric g f hf) z
```

**B6** (W-level producer of B6d's `hW`; 150–250 lines; namespace `Surgery.Topology.ObservedHistory`;
imports Transfer and Witnesses). It uses:
- the stage witness;
- `SpatialCanonicalWitness.scaleMetric`;
- `neckAlternatives_of_spatialCanonicalWitness` (Transfer:940);
- B5 with `g := scaleMetric R (stage metric at v)`, `f := f j`, `r := 1`;
- `localPullMetric ∘ scaleMetric` commutation.
```lean
theorem exists_neckAlternatives_of_survivor_maps :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) {R θ t₀ qs qW L : ℝ}
      (hR : 0 < R) {eps C1 C2 : ℝ} (hqs : qs ≤ R * qW) (hL : 0 < L)
      {W : TopologicalSpace.Opens (H.stageAt t).Carrier}
      {h : ℝ → SmoothRiemannianMetric ThreeModel W}
      (a : Icc (0 : ℝ) H.horizon) (ha : (a : ℝ) = t - θ / R)
      (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
        (H.stage j.val).Carrier)
      (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j)),
      (∀ j, Injective (f j)) →
      (∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
        (t : ℝ) + s / R ∈ H.stageDomain j.val →
          h s = scaleMetric R hR
            (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j))) →
      (∀ v : Icc (0 : ℝ) H.horizon, (v : ℝ) < t₀ → H.time (H.activeStage v) < v →
        ∀ p : (H.stageAt v).Carrier, qs < metricScalarAt (H.stageMetric (H.activeStage v) v) p →
          ∃ Wt : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 p,
            Wt.capTubeHasNeckChart eps) →
      ∀ {s : ℝ}, s ∈ Icc (-θ) 0 → (t : ℝ) + s / R < t₀ →
      (∀ hv : (t : ℝ) + s / R ∈ Icc (0 : ℝ) H.horizon,
        H.time (H.activeStage ⟨_, hv⟩) < (t : ℝ) + s / R) →
      ∀ z : W, IsCompact (riemannianClosedBallOf (h 0) z 1) →
      (∀ y ∈ riemannianClosedBallOf (h 0) z 1, ∀ u : TangentSpace ThreeModel y,
        (h 0).inner y u u ≤ L ^ 2 * (h s).inner y u u) →
      qW < metricScalarAt (h s) z →
      L * (max (2 * |C1|) C2 + (D + 2 * eps⁻¹) * Real.sqrt (max (2 * |C1|) C2)) <
        Real.sqrt (metricScalarAt (h s) z) →
      Nonempty (SpatialNeck (h s) eps z) ∨
        (∃ w : W, Nonempty (SpatialNeck (h s) eps w) ∧
          metricScalarAt (h s) z ≤ max (2 * |C1|) C2 * metricScalarAt (h s) w ∧
          metricScalarAt (h s) w ≤ max (2 * |C1|) C2 * metricScalarAt (h s) z ∧
          riemannianEDistOf (h s) z w <
            ENNReal.ofReal (max (2 * |C1|) C2 / Real.sqrt (metricScalarAt (h s) z))) ∨
        ∀ y ∈ connectedComponent z,
          metricScalarAt (h s) y ≤ max (2 * |C1|) C2 * metricScalarAt (h s) z
```

**B7** (B6b′ exports; edit of `TracedRegionAncientLimitData.lean:321`; 530–1060 lines). Add three
clauses to B6b′'s conclusion.

- **(vi) Time-Lipschitz.** This is the elaborated conjunct, inserted after the per-`k` block:
  ```lean
  (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
    ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ z : W k n, (z : (X.obj n).M) ∈
        riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
      ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
  ```
  Proof sources:
  - The pointwise core of `exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds`
    (`Estimates/InitialMetricTimeBounds.lean:100`), on the forward-shifted flow `h(−(k+1) + ·)`.
  - `hgram` on `Icc`: from `IsSolutionOn (h k n)` on the open window, plus the slab's
    `MetricSmoothUpTo` near `tₙ` through identity (iii).
  - `MovingShiBoundOn`: from the traced region's jets (the private `exists_curvDerivNorm_bound_of_window`).
  - Uniform equivalence: from `|Rm| ≤ K`.
  - Reference change from `h(−(k+1))` to `h(0)`: 400–800 lines.
- **(vii) Scalar bound.** `∀ k, ∃ B, ∀ᶠ n, ∀ s ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0, ∀ x : W k n,
  metricScalarAt (h k n s) x ≤ B`, from the survivor data's `curvDerivNormSq 0 ≤ K²`: 30–60 lines.
- **Lower bound.** Then B2 + B3 + (vii) + pinching give `∀ k, ∀ᶠ n, ∀ s ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
  ∀ y u, (h k n 0).inner y u u ≤ Real.exp 2 * (h k n s).inner y u u`: 100–200 lines.

**B8** (convergence at shifted times; 200–350 lines). It uses:
- `metricDerivNorm` naturality under `localPullMetric`;
- `exists_metric_reference_change_delta` (from `h(0)` to `P.metric`, through `hconv` at `t = 0`);
- `metricDerivNorm_triangle` (`Geometry/Metric/Convergence/CovariantDerivative/Algebra.lean:206`);
- `F.eventually_image_closed_ball_subset` to place `φ(K)` in the `(k+2)`-ball.

The hypothesis `hh0` used in the probe is not needed: `hconv` at `t = 0` together with `hG0` supplies
the reference. Statement with `hh0` dropped:
```lean
theorem tendsto_metricDerivNormSupOn_localPull_shifted_of_time_lipschitz
    {X : PointedRiemannianSeq.{w, 0, 0} I3} {P : PointedRiemannianManifold.{w, 0, 0} I3}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    (F : PointedRiemannianConvergenceMaps X P f) {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
    (hφF : ∀ k j (hj : N k ≤ j) (z : V k),
      ((φ k j hj z : W k (f j)) : (X.obj (f j)).M) = F.map j z)
    {G : ℝ → SmoothRiemannianMetric I3 P.M} (hG0 : G 0 = P.metric) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ)
    (hconv : ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        metricDerivNormSupOn K p
          (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
    (hLip : ∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
        ∀ z : W k n, (z : (X.obj n).M) ∈
            riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
          ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|)
    {s : ℝ} (hs : s ≤ 0) {σ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 s)) (hσs : ∀ n, σ n ≤ s)
    (k : ℕ) (hk : -((k : ℕ) : ℝ) ≤ s) (K : Set (V k)) (hK : IsCompact K) (p : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
      σ (f (ψ i)) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 ∧
      metricDerivNormSupOn K p
        (localPullMetric (h k (f (ψ i)) (σ (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
        ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η
```

**B9** (per-point transfer at shifted times). This is a copy-edit of `neck_alternatives_of_local_flow_limit`
(Transfer:1186); the delta is 100–200 lines. Its signature is identical except:
- drop `hconv` and `hEreg`;
- add
  ```lean
  {σ : ℝ → ℕ → ℝ} (hσE : ∀ s ≤ 0, ∀ᶠ n in atTop, σ s n ∉ E n)
  (hconvσ : ∀ s ≤ 0, ∀ k : ℕ, -((k : ℕ) : ℝ) ≤ s → ∀ (K : Set (V k)), IsCompact K →
    ∀ p : ℕ, ∀ η : ℝ, 0 < η → ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
      σ s (f (ψ i)) ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0 ∧
      metricDerivNormSupOn K p
        (localPullMetric (h k (f (ψ i)) (σ s (f (ψ i)))) (φ k (ψ i) hi) (hφ k (ψ i) hi))
        ((G s).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η)
  ```

The conclusion is unchanged: 2α-neck alternatives at every `s ≤ 0` above `4·max q 1`. In the proof,
`seq k i := φ*h k (fψi) (σ s (fψi))` and `hW` is applied at `σ s (fψi)`. B1 supplies `σ` and B8
supplies `hconvσ`.

**B10** (Part A with a sliver; 50–120 lines):
- `abs_derivWithin_scalar_le_of_local_flow_limit` takes `(hζ : Tendsto ζ atTop (𝓝 0))
  (hE : ∀ n, (E n \ Icc (-(ζ n)) 0).Finite)` in place of `(∀ n, (E n).Finite)`.
- At `t < 0`, shrink the Lipschitz window to `[t − δ, t + δ]` with `t + δ < 0`.
- Eventually `ζₙ < −(t + δ)`, so only finitely many exceptional points remain in the window.

**B11** (restated B6d headline, `exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants_of_time_lipschitz`;
60–100 lines).
- It is the current headline (Transfer:1387) with `(∀ n, (E n).Finite) → (∀ s ≤ 0, ∀ᶠ n, s ∉ E n)`
  replaced by the block below, placed after `hpinch`. `hW` and `hderiv` are unchanged.
  ```lean
  (∀ k p : ℕ, ∃ L : ℝ, ∀ᶠ n in atTop, ∀ σ ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
    ∀ σ' ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
      ∀ z : W k n, (z : (X.obj n).M) ∈
          riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint ((k + 2 : ℕ) : ℝ) →
        ∀ a : ℕ, a ≤ p → metricDerivNorm a (h k n σ) (h k n σ') (h k n 0) z ≤ L * |σ - σ'|) →
  ∀ {E : ℕ → Set ℝ} {ζ : ℕ → ℝ}, Tendsto ζ atTop (𝓝 0) →
  (∀ n, (E n \ Icc (-(ζ n)) 0).Finite) →
  ```
- Proof: B9 via B1 and B8, then B10, then the existing slice-bound and Harnack steps.

**B12** (B6B3 lemmas 3 and 4 with cutoff `t₀`; 40–80 lines):
- `hstage` and `hcurrent` range over `v < t₀`, and the conclusion needs `t + s/R < t₀`.
- `hcurrent` becomes `DerivativeBoundBefore Ctime qcan t₀`.
- The final slab is treated in the same way.

**B13** (the composed headline; 250–450 lines; namespace `Surgery.Topology.ObservedHistory`; needs the
local instances of `TracedRegionAncientLimitData.lean:32–46`). It is stated from history hypotheses
only, and extends B6b′'s existential with the bound:
```lean
theorem exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before :
    ∃ epsW : ℝ, 0 < epsW ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    (htraced : ∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hnc : ∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
      (v : ℝ) ≤ t n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
          ((H n).stageMetric ((H n).activeStage v) v)
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
      ∀ x : ((H n).stageAt v).Carrier,
        curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
          (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x)))
    {t₀ : ℕ → ℝ} (ht₀ : ∀ n, t₀ n ≤ t n)
    (hsliver : Tendsto (fun n => R n * (t n - t₀ n)) atTop (𝓝 0))
    {eps C1 C2 Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ}, 0 < eps → eps ≤ epsW →
    (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
    (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
      (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
        qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
        ∃ W : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) eps C1 C2 p,
          W.capTubeHasNeckChart eps) →
    (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
      (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
        qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
        |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v') p)
          (Iic (v : ℝ)) v| ≤
          Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p ^ 2) →
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel := …   -- verbatim B6b′ (:334–339)
    ∃ (W …) (h …), (…B6b′ per-k block, verbatim…) ∧
      ∃ (f : ℕ → ℕ), StrictMono f ∧ ∃ P F, (∃ C, …) ∧ MetricComplete P ∧ ConnectedSpace P.M ∧
        (…) ∧ ∃ V N, (…) ∧ (…) ∧ ∃ φ hφ, (…) ∧ ∃ G, G 0 = P.metric ∧ IsSolutionOn … ∧
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (…B6b′ convergence clause…) ∧
            ∃ C : ℝ, ∀ s ≤ 0, ∀ x : P.M, metricScalarAt (G s) x ≤ C
```
The elided parts are B6b′'s conclusion verbatim (:334–408). The probe used the full text; the only
change is that the convergence clause is parenthesised before `∧ ∃ C`.

Proof plan for B13:
- `epsW` is B11's.
- `E n := Iic 0 ∩ ({s | t₀ n ≤ t n + s / R n} ∪ {s | ∃ i, t n + s / R n = (H n).time i})` and
  `ζ n := R n * (t n − t₀ n)`. Then `E n \ Icc (−ζ n) 0` is finite, being the image of
  `Fin (eventCount + 1)`.
- Constants:
  - `qW := max Cs (e·(C + (D + 2ε⁻¹)√C))²` with `C := max (2|C1|) C2`;
  - `qD := Cq`;
  - `L := e`, from B7's lower bound.
- Compactness of the unit `h(0)`-ball: it lies inside the `(k+2)`-ball of the compact stage, which is
  contained in `W`.
- `hW` comes from B6 and `hderiv` from B12 with B6B3 lemma 3.
- Pinching on `h`: `curvatureOperatorLowerBoundAt_scaleMetric` and
  `curvatureOperatorLowerBoundAt_localPullMetric_iff`, with `Q := R`.
- Then B7 (vi) and B11.

**Supplying B13 from the Crossing leaf.**
- `hwit`: `EventSlabsSpatiallyCanonical` + `SpatiallyCanonicalBefore t₀`, through a stage-level
  bridge shaped like B6B3 lemma 4.
- `hsliver`: from B1, `exists_sliver_forward_comparison` with `ζₙ = 1/(n+1)`. It gives
  `R·η ≤ ζ` on `[t₀, t₀ + η]`, hence `Rₙ(tₙ − t₀ₙ) ≤ ζₙ`.
- `εbar ≤ epsW` in `CrossingContinuation`.
- `qsₙ ≤ Cs·qcanₙ < Cs·Rₙ`.

## 3. Order and size

1. Parallel now: B1, B2, B3, B4, B12.
2. B5, after B4.
3. B6, after B5.
4. B7, the heaviest; it needs the private jets of B6b′.
5. B8, then B9, B10, B11.
6. B13.

Total about 1.9–3.4k lines. No interface change to `CrossingContinuation` is required. F-g (B3e at the
base slice) is outside this design and is flagged to the lead.
