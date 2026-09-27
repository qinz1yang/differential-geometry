# Design: the complete brick list closing `crossingContinuation`, 2026-09-26

Read-only design on `codex/pc-target-c-psf` @ 481017246 plus the uncommitted lanes as of 10:45 (BS1/BS6
files, `TracedRegionAncientLimitTimeControl.lean` with the κ-before-`t₀` variant renamed to
`exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before` at :781,
`AncientPointedFlowLimitShiftedTransfer.lean` with B8–B11 at :205/:354/:551, B13 started in
`TracedRegionAncientLimitScalarBound.lean:42`). Paths are relative to `DifferentialGeometry/Geometry/Flow/RicciFlow/`.

Every Lean statement in §2 was elaborated with a `sorry` body. There were two scratch probes outside
the tree, compiled with `lake env lean -DmaxSynthPendingDepth=3` and `LEAN_NUM_THREADS=2` against the
shared build (Leaves, B6b′ Data, B8, B3d constants, prefix transport):
- probe A has 9 declarations;
- probe F has 18 declarations and took 56 s.

Both produced only `declaration uses sorry` and have been deleted. The target is
`CrossingContinuation` (`Surgery/Topology/CanonicalNeighborhoodContinuationLeaves.lean:232`). Its
sorry stub is `theorem crossingContinuation` at `Surgery/Skeleton/PoincareEndgame.lean:44`. The binder order after M6 has been checked:
`∃ εbar`, then `∀ B ε`, then `∃ C1₀ C2₀ τ₀ Ctime₀ Cgrad₀`, then `∀ C1 … Cgrad, C1s C2s Cs, κ phi θ`,
then `∃ Dcap θcap q₀ mcap`, then `∀ qcan`, then `∃ δmax ρmax εcap`, then `∀ qs …`.

## 0. Failures first

**F1. Review G item 6: the witness clause is vacuous when `θ ≤ τmin`.** This is not a defect of the
leaf.
- At a bad point the leaf must refute the conjunction of three clauses:
  - the derivative clause (always);
  - the gradient clause (always);
  - the witness clause, but only when `τmin ≤ R(t − a)` (which forces `τmin < θ`).
- B8 supplies all three:
  - `eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit` (`AncientLimitCanonicalWitness.lean:533`)
    gives the derivative and gradient clauses with no age condition;
  - `exists_canonicalWitness_of_ancient_pointed_flow_limit` (`:117`) gives the witness once
    `τ₀(ε) ≤ R(t − a)`, and the leaf sets `τ₀ := τ₀(ε) ≤ τmin`.

However, B8 `:117` assumes the window hypothesis `∀ᶠ n, Icc (tₙ − τ₀/Rₙ) tₙ ⊆ carrier` for the
**whole** approximating sequence. So the age split must be made **before** the limit is built:
- pass to a subsequence with `τ₀ ≤ Rₙ(tₙ − aₙ)` for all `n`, or to one with `Rₙ(tₙ − aₙ) < τ₀` for all `n`;
- this is the hypothesis `hmode` of X5.

It cannot be done afterwards along `f ∘ ψ`.

**F2. M7(c) `Rₙtₙ → ∞`: TRUE, and the tree has the lower bound.** Two existing results give it:
- `ObservedHistory.event_time_gap_of_scalar_upper_bound` (`Surgery/Topology/HistoryCurvatureTimeBound.lean:61`,
  records' `singular` field): `time 1 − time 0 ≥ c(sup R(g₀), a₀)`;
- `OrientedThreeStage.exists_uniform_initial_curvature_bound` (`Surgery/Topology/InitialSlabUniformBounds.lean:21`):
  `R ≤ K` on `[0, η]`.

Together they give X0: `R ≤ K` at every time `t < η₀` in every class history. Consequences:
- bad points satisfy `tₙ ≥ η₀` as soon as `qcanₙ > K`, so `Rₙtₙ ≥ (n+1)η₀`;
- X0 subsumes BS7 (`t₀ = a = 0`, `InitialSlabScalarWindow.lean:14`) and every case `t₀ₙ < η₀`.

**F3. The `Λ ≤ R·t₀` supply for BS5/BS6** is `Rₙt₀ₙ ≥ Rₙtₙ − Rₙηₙ ≥ (n+1)η₀ − 1/(n+1)`, from X0 and
the sliver clause `R·η ≤ 1/(n+1)`. It is stated as `tendsto_scalar_mul_time_atTop`. In Case II the
same bound serves `Λ ≤ R·H.time j.succ`, because `t₀ = a` there.

**F4. The splits.** Four splits arise; only the age split needs a subsequence.

| Split | Handling | Subsequence? |
|---|---|---|
| Event slab vs terminal slab | The event case is reduced to terminal form by `prefixAt`, exactly as the event B3e (`BoundedCurvatureAtDistanceSliceEvent.lean:18`) reduces to the terminal one. The five missing prefix transports are X1e. The whole sequence is then terminal-form. | No |
| Case I (`t₀ > a`) vs Case II (`t₀ = a`) | Per-`n` dispatch inside X3p: BS5-terminal (`BoundedCurvatureAtDistanceSliver.lean:69`) or BS6 (`BoundedCurvatureAtDistanceAfterEvent.lean:45`, `Gk := G`, `last = j.succ`). The constants `(Q, Λ, Dcap, Rrad, ζ₀)` are the max/min over the two. | No |
| `t₀ = a = 0` | Excluded by X0. | No |
| Age mode | F1. | **Yes** |

**F5. hRP (M4): the rebased B3e is not delivered, and the escape-point recentring cannot be dropped.**
- **Base-centred replacement is circular.** On the partial limit `R(p, s)` is bounded only by the
  Harnack rate `T*Q₀/(s + T*)`. That is exactly the blow-up to be excluded, so a base-centred
  `∀ D, ∃ C, d_s(p, x) ≤ D → R(x, s) ≤ C` is as strong as the conclusion.
- **H9's device does not transfer.** It applies B3e at a centre known to be ¬CWP and pushes the ball
  away from a cap. In M4 the anchors are escape points of the far field, at depth `s → −T*`, where
  ¬CWP is not known.
- **The needed replacement is X4d.** This is bounded curvature at bounded distance anchored at an
  arbitrary point on a slice that carries "before" data, **with no ¬CWP hypothesis**. The proof must
  add the young-cap branch:
  - if the rebase point is not a CWP, use B3e as delivered;
  - if it is a `CWP(D₁, θ)` point, use the standard-cap window, whose curvature is comparable to the
    cap scale on the window
    (`exists_standard_comparison_of_cap_window_trace`, `CapWindowStandardComparison.lean:20`, and
    `exists_standard_scalar_lower_bound`, `Perelman/StandardSolution/StandardTerminalBlowup.lean:61`).
- The "window exit" is handled by an enlarged window, as in H9.
- **X4d is the risk item of this design (§4).**
- A retraction: my first suspicion was a counterexample (a young cap tip next to an anchor). It is
  not one, because on the standard solution every curvature on a bounded region is comparable to
  `λ/(1−τ)`. The upper half of this claim is to be confirmed by the review.

**F6. The windowed B6b′ depth is FALSE as sketched.** B6b′/TimeControl use traced depth `2(k+2)` to
produce flows on `[−(k+2), 0]`: the survivor maps live on twice the flow window. A windowed copy fed
only depths `< T*` therefore covers `(−T*/2, 0]`, not `(−T*, 0]`. W1 repairs this:
- traced depth `τ k`;
- flows and survivor maps on `[−τ k, 0]`;
- Lipschitz, κ and convergence windows on `[−((k+1)/(k+2))·τ k, 0]` (Shi needs only a positive margin).

**F7. M3 as written in DESIGN_MAXWINDOW §3.2b is FALSE in its step 5.** No spatial witnesses exist on
the time-0 slice: the sliver carries no data. The time-zero limit must therefore be a *flow* limit
with a `k`-dependent depth `τ_k ↓ 0`, taken from the per-radius bounds X3p via W1. Witnesses at
`s = 0` then come by the shifted-time transfer, per `k`. This route handles Case II with no extra
work, because the survivor flows cross the event and the pre-event slices carry witnesses.

**F8. M6's `Cbirth` republish is unnecessary.**
- Choose `ρmaxₙ² ≤ min (1/(2(n+1)qcanₙ)) ρs(qcanₙ)²` after `qcanₙ`.
- `inv_two_mul_sq_lt_static_scale` (`CanonicalNeighborhoodContinuationLeaves.lean:77`) then gives
  `scale ≥ (n+1)·qcanₙ` (context field `hscale`).
- So `2qcanₙ ≤ Cbirth·scale` and `1 ≤ a₀·scale` hold eventually for every fixed `(Θ, Cbirth)`.
- B5 (`TracedRegionOrCapWindow.lean:665`) is therefore used as published, with `Θ := (θcap_B5 + 1)/2`
  fixed per `(T, Q)`.

**F9. The `t₀ = a` twin of BS2 is not delivered.** Only its derivative clause is consumed (B5's
`hcurrent`). The supplier chain is `RetainedCoreHistory.exists_slice_bounds_at_slab_start`
(`SlabStartDerivativeBounds.lean:94`) followed by `exists_derivativeBoundBefore_extend_of_slice`
(`DerivativeBoundExtension.lean:66`), as in `CapWindowContinuationLeaf.lean:307`. X1 takes the result
as `hext`. This imposes constant constraints:

| Constraint | Source |
|---|---|
| `Ctime₀ ≥ Cs_start` | slab-start derivative bound |
| `Dcap ≥ Rs`, `mcap ≥ ms`, `q₀ ≥ qs_start` | slab-start bounds, chosen before `qcan` |
| `δs ρs εs` | taken after `qcan` |

**F10. B8 needs further inputs.** None of the following is produced today:
- `TangentOrientationSection P.M` (X5c);
- `metricScalarAt P.metric P.basepoint = 1` (X5d);
- a flow `S n` on `(stageAt tₙ).Carrier`: use `closedPrefixAt` of the extended history
  (`HistoryRestriction.lean:192`) and transport back to `G.flow` by X6b (HEq along
  `activeStage = last`).

**F11. Terminal form needs records and CWP under `extendHorizon` (M7(d)).** This is
`capWindowPoint_extendHorizon_iff`, which also carries the class family and the scales.

## 1. Constants and the contradiction sequence

The leaf's constant choices:

| Constant | Value | Source |
|---|---|---|
| `εbar` | `min coneAccuracy (min epsW (windowFarAccuracy / 2))` | `coneAccuracy` from B3d constants; `epsW` from X5 (= B11's); `windowFarAccuracy` from X4a |
| `C1₀ = C2₀ = Cgrad₀` | `C` | X5, at `ε` |
| `Ctime₀` | `max C Cs_start` | X5 and F9 |
| `τ₀` | X5's `τ₀` | X5 |

Negate the tail after `θ` and instantiate the existentials with:
- `Dₙ := max (n+1) Rs`;
- `θcapₙ := 1 − 1/(n+2)`;
- `q₀ₙ := max (n+1) qs_start`;
- `mcapₙ := max (n+2) ms`;
- `δmaxₙ, εcapₙ := min (1/(n+1)) (δs, εs)(qcan)`, with `ρmaxₙ` as in F8.

For each `n`, then:
1. X1 (event case through `prefixAt` and X1e) gives the terminal-form data of the context `Σ` (§2.3),
   with `ζ = 1/(n+1)`, `ζ' = qcanₙ/4` and `ς = 1/(n+2)`.
2. `Rₙ := R(tₙ, yₙ) > qcanₙ ≥ n+1`.
3. Split by age mode (F1).
4. `E σ T :=` `DepthExtendable` of the extended histories `Kₙ := Hₙ.extendAt …`.
5. X2 (maximal depth) with base case X3.
6. Finite `T*`: X4 then X4ext contradict maximality.
7. `T* = ∞`: X5 then X6b give the three clauses at `(yₙ, tₙ)`, contradicting the bad clause from X1.

## 2. Statements (all elaborated)

Namespace `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology`. The opens are those of the
`TracedRegionAncientLimitData` header plus `…FiniteHorn`. Statements under `PointedRiemannianManifold`
use the Data file's local instances; W1 also uses its private `Opens` instances.

### 2.1 X0: initial window (M7(c); new file `InitialWindowScalarBound.lean`, 80–150 lines)
```lean
theorem RetainedCoreHistory.exists_scalar_le_before_initial_window (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) :
    ∃ η₀ K : ℝ, 0 < η₀ ∧ ∀ (B : ℝ) (p₀ : CutoffParameters) (δbound ρbound : ℝ)
      (H : RetainedCoreHistory P₀), H.InCutoffClass g₀ B p₀ δbound ρbound →
      (∀ (j : Fin H.eventCount) (t : ℝ) (y : (H.stage j.castSucc).Carrier),
        H.time j.castSucc ≤ t → t < H.time j.succ → t < η₀ →
          (H.toHistory.event j).incoming.flow.scalar t y ≤ K) ∧
      ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s),
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) →
        ∀ (t : ℝ) (y : (H.stage (Fin.last H.eventCount)).Carrier),
          H.time (Fin.last H.eventCount) ≤ t → t < s → t < η₀ → G.flow.scalar t y ≤ K
```

### 2.2 X1: bad point and sliver packaging, per history (X1 120–200, X1e 80–150, X1k 150–300)
```lean
theorem RetainedCoreHistory.exists_crossing_bad_point_terminal {P₀ : OrientedThreeStage.{u}}
    (H : RetainedCoreHistory P₀) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    {p : CutoffParameters} (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
    {ε C1 C2 qcan τmin θ Dcap θcap ζ ζ' ς : ℝ} {Ctime Cgrad : ℝ≥0}
    (hζ : 0 < ζ) (hζ' : 0 < ζ') (hς : 0 < ς) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (H.time (Fin.last H.eventCount)) s)
    (hext : ∃ η₀ : ℝ, 0 < η₀ ∧ t₀ + η₀ < s ∧
      G.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t₀ + η₀))
    (hfail : ¬ ∃ η : ℝ, 0 < η ∧ G.CanonicalBoundsOn ε C1 C2 qcan τmin Ctime Cgrad t₀ η
      fun y t => G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap) :
    ∃ η : ℝ, 0 < η ∧ t₀ + η < s ∧
      G.DerivativeBoundBefore (2 * Ctime) (2 * qcan) (t₀ + η) ∧
      (∀ t ∈ Icc t₀ (t₀ + η), ∀ x : (H.stage (Fin.last H.eventCount)).Carrier,
        G.flow.scalar t x * η ≤ ζ ∧ |G.flow.scalar t x - G.flow.scalar t₀ x| ≤ ζ' ∧
        ∀ v : TangentSpace ThreeModel x,
          (G.flow.base.metric t).inner x v v ≤
            Real.exp 1 * (G.flow.base.metric t₀).inner x v v ∧
          (G.flow.base.metric t₀).inner x v v ≤
            Real.exp 1 * (G.flow.base.metric t).inner x v v) ∧
      (∃ S : ℝ, 0 < S ∧ (∀ i b, ((records i).static b).neck.scale ≤ S) ∧ S * η ≤ ς) ∧
      ∃ (y : (H.stage (Fin.last H.eventCount)).Carrier) (t : ℝ),
        H.time (Fin.last H.eventCount) < t ∧ t₀ ≤ t ∧ t < t₀ + η ∧
        qcan < G.flow.scalar t y ∧
        G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) < θ ∧
        ¬ H.CapWindowPoint records (Fin.last H.eventCount) y t Dcap θcap ∧
        ¬ ((τmin ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) →
              ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
            |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤
              Ctime * G.flow.scalar t y ^ 2 ∧
            ∀ v : TangentSpace I3 y,
              |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
                Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
                  Real.sqrt ((G.flow.base.metric t).inner y v v))
```
Suppliers:
- BS1 `exists_forall_Icc_scalar_riemannNorm_metric_close` (`SlabTimeWindowContinuity.lean:49`, `Ico`, so `t₀ = a` is allowed);
- `exists_sliver_forward_comparison` (`SliverForwardComparison.lean:262`);
- BS4 `exists_forall_neck_scale_le` (`CapWindowPointTimeSlack.lean:34`).

X1e is the set of prefix transports, all elaborated. Their conclusions are at `(H.prefixAt k)` and
`Fin.last _`:
- `inCutoffClass_prefixAt (hH) (k)`;
- `eventSlabsSpatiallyCanonical_prefixAt (k) (h : …SpatiallyCanonical ε C1 C2 q k)`;
- `eventSlabsCanonical_prefixAt`;
- `eventSlabsGradient_prefixAt`;
- `noncollapsedBefore_prefixAt (k) (h : H.NoncollapsedBefore κ ρ t) (ht : H.time k ≤ t) : (H.prefixAt k).NoncollapsedBefore κ ρ (H.time k)`.

These add to the existing `eventSlabsDerivative/Pinched_prefixAt`, `terminalNoncollapsedBefore_prefixAt`
and `capWindowPoint_of_prefixAt` (`RetainedCoreHistoryPrefixTransport.lean:177–216`).

X1k defines the extended history, a new file `Surgery/Topology/RetainedCoreHistoryExtendAt.lean`:
```lean
def RetainedCoreHistory.extendAt (H : RetainedCoreHistory P₀)
    (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {t : ℝ}
    (hat : H.time (Fin.last H.eventCount) < t) (hts : t < s) : RetainedCoreHistory P₀ :=
  H.extendHorizon t (hend ▸ hat.le) (G.closedPrefix t hat hts) hG
def RetainedCoreHistory.extendAtTime … : Icc (0 : ℝ) (H.extendAt hend G hG hat hts).toHistory.horizon :=
  ⟨t, (H.toHistory.time_nonneg _).trans hat.le, le_rfl⟩
theorem RetainedCoreHistory.capWindowPoint_extendHorizon_iff (H) (records) {T} (hT) (S) (hS) :
    ∃ records' : ∀ i, GeometricCutoffRecord (H.extendHorizon T hT S hS).toHistory i p,
      (∀ p₀ δ₀ ρ₀, H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records →
        (H.extendHorizon T hT S hS).IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records') ∧
      (∀ i b, ((records' i).static b).neck.scale = ((records i).static b).neck.scale) ∧
      ∀ y t D θ, (H.extendHorizon T hT S hS).CapWindowPoint records' (Fin.last _) y t D θ ↔
        H.CapWindowPoint records (Fin.last H.eventCount) y t D θ
```
(The elaborated binder lists are those of `extendAt`.) `extendAt` is literally the history of
`TerminalNoncollapsedBefore` (`CanonicalNeighborhoodInduction.lean:196`).

### 2.3 The sequence context `Σ` (a `variable` block; X3p, X3a, X3, X4, X4ext and the F3 lemma)
```lean
variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {B ε C1 C2 τmin θ κ C1s C2s Cs : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D θcap qcan qs η t₀ t s : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory P₀}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
    ((H n).time (Fin.last (H n).eventCount)) (s n)}
  {y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier}
  (hε : 0 < ε) (hεcone : ε ≤ coneAccuracy) (hεfar : 2 * ε ≤ windowFarAccuracy)
  (hκ : 0 < κ) (hphi : Perelman.AdmissiblePinchingFunction phi) (hθ : 0 < θ)
  (hCs : 1 ≤ Cs) (hCt : 0 < Ctime)
  (hH : ∀ n, (H n).InCutoffClass g₀ B (p₀ n) (δb n) (ρb n))
  (hG : ∀ n, (H n).IsContinuationSlab B (Fin.last (H n).eventCount) (G n))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n ∧ qcan n ≤ qs n ∧ qs n ≤ Cs * qcan n)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((records n i).static b).neck.scale)
  (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi ∧
    Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
  (hslabs : ∀ n,
    (H n).EventSlabsCanonical ε C1 C2 (qcan n) τmin (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsDerivative Ctime (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsGradient Cgrad (qcan n) (Fin.last (H n).eventCount) ∧
    (H n).EventSlabsSpatiallyCanonical ε C1s C2s (qs n) (Fin.last (H n).eventCount) ∧
    (H n).NoncollapsedBefore κ ε ((H n).time (Fin.last (H n).eventCount)))
  (hbefore : ∀ n, t₀ n ∈ Ico ((H n).time (Fin.last (H n).eventCount)) (s n) ∧
    (G n).CanonicalBefore ε C1 C2 (qcan n) τmin (t₀ n) ∧
    (G n).DerivativeBoundBefore Ctime (qcan n) (t₀ n) ∧
    (G n).GradientBoundBefore Cgrad (qcan n) (t₀ n) ∧
    (G n).SpatiallyCanonicalBefore ε C1s C2s (qs n) (t₀ n) ∧
    (H n).TerminalNoncollapsedBefore (hH n).2.1 (G n) (hG n).2 κ ε (t₀ n))
  (hsliver : ∀ n, 0 < η n ∧ t₀ n + η n < s n ∧
    (G n).DerivativeBoundBefore (2 * Ctime) (2 * qcan n) (t₀ n + η n) ∧
    (∀ t' ∈ Icc (t₀ n) (t₀ n + η n), ∀ x, (G n).flow.scalar t' x * η n ≤ 1 / ((n : ℝ) + 1) ∧
      |(G n).flow.scalar t' x - (G n).flow.scalar (t₀ n) x| ≤ qcan n / 4 ∧
      ∀ v : TangentSpace ThreeModel x,
        ((G n).flow.base.metric t').inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric (t₀ n)).inner x v v ∧
        ((G n).flow.base.metric (t₀ n)).inner x v v ≤
          Real.exp 1 * ((G n).flow.base.metric t').inner x v v) ∧
    ∀ i b, ((records n i).static b).neck.scale * η n ≤ 1 / ((n : ℝ) + 2))
  (hbad : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n ∧ t₀ n ≤ t n ∧
    t n < t₀ n + η n ∧ qcan n < (G n).flow.scalar (t n) (y n) ∧
    (G n).flow.scalar (t n) (y n) * (t n - (H n).time (Fin.last (H n).eventCount)) < θ ∧
    ¬ (H n).CapWindowPoint (records n) (Fin.last (H n).eventCount) (y n) (t n) (D n) (θcap n))
include hε hεcone hεfar hκ hphi hθ hCs hCt hH hG hrec hq hpar hscale hθcap hpinch hslabs hbefore
  hsliver hbad
```
The extended histories, which every `DepthExtendable` below refers to, are written inline as
```lean
    let K : ℕ → RetainedCoreHistory P₀ := fun n => (H n).extendAt (hH n).2.1 (G n) (hG n).2
      (hbad n).1 ((hbad n).2.2.1.trans (hsliver n).2.1)
    let τ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon := fun n =>
      (H n).extendAtTime (hH n).2.1 (G n) (hG n).2 (hbad n).1
        ((hbad n).2.2.1.trans (hsliver n).2.1)
    ∀ ŷ : ∀ n, ((K n).toHistory.stageAt (τ n)).Carrier, (∀ n, HEq (ŷ n) (y n)) → …
```
Below this header is abbreviated `⟪K τ ŷ⟫`, and `R n := (G n).flow.scalar (t n) (y n)`. The probe
statements carry it verbatim.

### 2.4 X2: maximal depth (M2; `Surgery/Topology/TracedRegionMaximalDepth.lean` and a generic `Order/` lemma, 150–300 lines)
```lean
def ObservedHistory.DepthExtendable (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ) (σ : ℕ → ℕ) (T : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ i in atTop,
    (H (σ i)).isTracedRegion (t (σ i)) (y (σ i)) (A / Real.sqrt (R (σ i))) (T / R (σ i))
      (K * R (σ i))
theorem DepthExtendable.mono_depth (h : DepthExtendable H t y R σ T) (hR : ∀ n, 0 < R n)
    (hT' : 0 < T') (hle : T' ≤ T) : DepthExtendable H t y R σ T'
theorem DepthExtendable.comp (h : DepthExtendable H t y R σ T) (hψ : StrictMono ψ) :
    DepthExtendable H t y R (σ ∘ ψ) T
theorem DepthExtendable.congr (h : DepthExtendable H t y R σ T)
    (hσ : ∀ᶠ i in atTop, σ i = σ' i) : DepthExtendable H t y R σ' T
theorem exists_strictMono_forall_of_subseq_property (E : (ℕ → ℕ) → ℝ → Prop)
    (hdown : ∀ σ T T', 0 < T' → T' ≤ T → E σ T → E σ T')
    (hsub : ∀ σ ψ T, StrictMono ψ → E σ T → E (σ ∘ ψ) T)
    (htail : ∀ σ σ' T, (∀ᶠ i in atTop, σ i = σ' i) → E σ T → E σ' T) (σ₀ : ℕ → ℕ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ χ : ℕ → ℕ, StrictMono χ → ∀ T T' : ℝ, 0 < T' → T' < T →
      E (σ₀ ∘ ψ ∘ χ) T → E (σ₀ ∘ ψ) T'
theorem exists_strictMono_maximal_depth (E) (hdown) (hsub) (htail) (σ₀ : ℕ → ℕ)
    (hbase : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T₀ : ℝ, 0 < T₀ ∧ E (σ₀ ∘ ψ) T₀) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ T : ℝ, 0 < T → E (σ₀ ∘ ψ) T) ∨
        ∃ Tstar : ℝ, 0 < Tstar ∧ (∀ T : ℝ, 0 < T → T < Tstar → E (σ₀ ∘ ψ) T) ∧
          ∀ χ : ℕ → ℕ, StrictMono χ → ∀ T : ℝ, Tstar < T → ¬ E (σ₀ ∘ ψ ∘ χ) T)
```
The first generic lemma uses nested subsequences over an enumeration of the positive rationals, then
the diagonal `ψ i := ψ_i i`. The diagonal is eventually a subsequence of each stage, which is why
`htail` is needed. The second lemma separates the finite and infinite cases with no `sSup` on
unbounded sets (review G item 1). The `hbase` hypothesis is supplied by X3.

### 2.5 X3: time-zero bound and base case (M3)
```lean
theorem eventually_scalar_le_on_normalized_ball_at_base :            -- X3p, per-n BS5/BS6 dispatch
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
          (A / Real.sqrt ((G n).flow.scalar (t n) (y n))),
        (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (y n)
theorem tendsto_scalar_mul_time_atTop :                               -- F3
    Tendsto (fun n => (G n).flow.scalar (t n) (y n) * t₀ n) atTop atTop
theorem exists_subseq_scalar_le_on_normalized_balls_at_base (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ z ∈ riemannianBallOf ((G (σ (ψ i))).flow.base.metric (t (σ (ψ i)))) (y (σ (ψ i)))
          (A / Real.sqrt ((G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))))),
        (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) z ≤
          C₀ * (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i)))
theorem exists_subseq_depthExtendable_pos (σ : ℕ → ℕ) (hσ : StrictMono σ) : ⟪K τ ŷ⟫
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T₀ : ℝ, 0 < T₀ ∧
      ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
        (fun n => (G n).flow.scalar (t n) (y n)) (σ ∘ ψ) T₀
```
Routes:
- **X3p** (150–250 lines). Per `n`, apply BS5-terminal when `t₀ > a` and BS6 when `t₀ = a`, with
  `Cq = Cs`, `q = qs`, `ρ = ε` and `θ = 1/2`.
  - `¬CWP(y, t₀, Dcap, 1/2)` comes from `hbad`, then BS3 `CapWindowPoint.of_le_time`
    (`CapWindowPointTimeSlack.lean:13`, slack `1/(n+2)`), then `CapWindowPoint.mono`
    (`…SliceTerminal.lean:326`).
  - `Λ ≤ R·t₀` comes from F3.
  - The derivative threshold is relaxed from `qcan` to `qs`.
- **X3a** (300–500 lines, plus W1 and a per-`k` B9):
  1. X3p at `A = k+4`, then the B7 step (`TracedRegionDepthInduction.lean:17`, with constants
     `(2Ctime, 2qcan)` from `hsliver`), then B5 at `tₙ`.
     - B5's right branch contradicts `hbad` through `mono`, since `Dₙ → ∞` and `θcapₙ → 1`.
     - This gives `isTracedRegion` at radius `k+4` and depth `τ_k := 1/(8·Ctime·Q_{k+4}) ↓ 0`.
  2. W1 with this schedule.
  3. Neck alternatives at `s = 0` through the shifted-time transfer on `V k`. This is B9
     (`neck_alternatives_of_local_flow_limit_at_shifted_times`, `AncientPointedFlowLimitShiftedTransfer.lean:354`)
     with `G` replaced by `Gloc k` on `V k`; it is a copy-edit, and only the per-point argument is used.
  4. `Rm ≥ 0` at time 0, from `curvatureOperator_nonnegative_of_local_pinching_limit`
     (`AncientPointedFlowLimitCurvature.lean:26`).
  5. `exists_scalar_bound_of_curvatureOperator_nonnegative_of_neck_alternatives`
     (`AncientPointedFlowLimitTransfer.lean:440`) on `(P, P.metric)`, which is complete and connected.
  6. `C⁰` pull-back to the normalized balls.
- **X3** (100–200 lines). `Q := 2C₀` and `T₀ := 1/(8·Ctime·C₀)`, then the B7 step and B5, as
  DESIGN_MAXWINDOW §3.3.

### 2.6 W1: B6b′ with a depth schedule (F6/F7/M7(a); new theorem next to TimeControl, 600–1000 lines of copied proof)

`exists_local_pointed_flow_limits_with_time_lipschitz_survivor_maps_of_depth_schedule` is exactly the
statement of `…_of_noncollapsed_before` (TimeControl:781) with the substitutions below. It elaborated.

Hypothesis change: add `(τ : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)` and replace `htraced` by
```lean
    (htraced : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 4 : ℕ) : ℝ) / Real.sqrt (R n)) (τ k / R n)
        (K * R n))
```

Conclusion changes, per-`k` block:

| Window or term | Before | After |
|---|---|---|
| `IsSolutionOn` window | `closed (-((k+2:ℕ):ℝ)) 0` | `closed (-τ k) 0 (neg_nonpos.mpr (hτ k).le)` |
| Current-slab identity | on `Icc (-((k+2:ℕ):ℝ)) 0` | on `Icc (-τ k) 0` |
| Survivor start | `a = t n − 2(k+2)/R n` | `a = t n − τ k / R n` |
| Survivor identities | on `Icc (-(2(k+2))) 0` | on `Icc (-τ k) 0` |
| κ-test, Lipschitz and `e²` windows | `Icc (-((k+1:ℕ):ℝ)) 0` | `Icc (-(((k+1:ℕ):ℝ)/((k+2:ℕ):ℝ) * τ k)) 0` |
| κ inclusion and scalar-bound window | `Icc (-((k+2:ℕ):ℝ)) 0` | `Icc (-τ k) 0` |
| Radii `k+3`, `k+2`, `(k+1)/2` | unchanged | unchanged |

The limit part replaces the glued `G` and its κ clause by per-`k` local limit flows:
```lean
              ∃ Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric ThreeModel (V k),
                (∀ k, Gloc k 0 = P.metric.restrictOpen (V k)) ∧
                (∀ k, IsSolutionOn ({ base.metric := Gloc k } :
                  SolutionOn (I := ThreeModel) (M := V k)
                    (RealTimeInterval.closed (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0
                      (neg_nonpos.mpr (mul_pos (by positivity) (hτ k)).le)))) ∧
                ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
                  ∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
                    ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i,
                      ∀ s ∈ Icc (-(((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) * τ k)) 0,
                        metricDerivNormSupOn K p
                          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
                          (Gloc k s) (P.metric.restrictOpen (V k)) < η
```
Uses:
- X3 with `τ_k ↓ 0`, with no gluing;
- X4 with `τ_k := T*·(k+1)/(k+2)`, glued by generalizing `exists_ancient_solution_of_compatible_open_cover`
  (`Solution/AncientGluing.lean:17`) to `openClosed (−T*) 0`. The per-`k` flows are compatible
  because `hφF` makes every `φ k j` agree with `F.map j`.

TimeControl:781 is the instance `τ k = 2(k+2)` up to the inner-window constant. When TimeControl is
merged, the lead should make it a corollary.

### 2.7 X4: the finite-window case (M4 and extension)
```lean
theorem exists_uniform_scalar_bound_on_openClosed_window_of_spatialCanonicalWitness :   -- X4a
    ∃ εfar : ℝ, 0 < εfar ∧ ∀ {P : PointedRiemannianManifold.{u, 0, 0} I3} [ConnectedSpace P.M]
      {Tstar : ℝ} (hT : 0 < Tstar) (G : ℝ → SmoothRiemannianMetric I3 P.M),
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        (RealTimeInterval.openClosed (-Tstar) 0 0 ⟨by linarith, le_rfl⟩)) →
      G 0 = P.metric →
      (∀ τ ∈ Ioc (-Tstar) 0, RiemannianMetricComplete (G τ)) →
      (∀ τ ∈ Ioc (-Tstar) 0, ∀ x : P.M,
        metricAlgebraicCurvatureTensorAt (G τ) x ∈ algebraicCurvatureOperatorNonnegativeCone) →
      ∀ {ε C1 C2 q : ℝ} {Ctime : ℝ≥0}, ε ≤ εfar →
      (∀ τ ∈ Ioc (-Tstar) 0, ∀ x : P.M, q < metricScalarAt (G τ) x →
        ∃ W : SpatialCanonicalWitness (G τ) ε C1 C2 x, W.capTubeHasNeckChart ε) →
      (∀ τ ∈ Ioo (-Tstar) 0, ∀ x : P.M, q < metricScalarAt (G τ) x →
        |derivWithin (fun v => metricScalarAt (G v) x) (Iic τ) τ| ≤
          Ctime * metricScalarAt (G τ) x ^ 2) →
      (∀ A Dd : ℝ, ∃ C : ℝ, ∀ τ ∈ Ioo (-Tstar) 0, ∀ z x : P.M,
        metricScalarAt (G τ) z ≤ A → riemannianEDistOf (G τ) z x < ENNReal.ofReal Dd →
          metricScalarAt (G τ) x ≤ C) →
      ∃ C : ℝ, ∀ τ ∈ Ioc (-Tstar) 0, ∀ x : P.M, metricScalarAt (G τ) x ≤ C
```
X4a (`Perelman/CanonicalNeighborhood/WindowScalarBound.lean`; 500–900 lines, plus a 700–1200-line
far-field port) is a bootstrap:
1. `Q₀` from B6d's per-slice theorem at `τ = 0`
   (`exists_scalar_bound_of_curvatureOperator_nonnegative_of_spatialCanonicalWitness`,
   `AncientPointedFlowLimitBoundedCurvature.lean:110`).
2. On each window `[a, 0]` that already carries a bound:
   `ricciFlow_additive_distance_bound_of_terminal_scalar` (`Estimates/Distance/TerminalScalar.lean:173`),
   with constant `(20/3)√(2T*Q₀)√T*`.
3. The far-field bound: a port of `exists_uniform_scalar_bound_outside_terminal_ball`
   (`Perelman/CanonicalNeighborhood/BackwardScalarExterior.lean:89`) that keeps the `herror` comparison.
4. At the escape point, the anchored `hRP` (the last hypothesis).
5. The derivative step `δ = 1/(2(Ctime+1)·max(C*, q))`.

It does not use Harnack (review G item 1). `windowFarAccuracy : ℝ` is a `def` in X4a's file, the
analogue of `coneAccuracy`, fixed as `(X4a).choose`. The leaf needs `2ε ≤ windowFarAccuracy`, because
the witness transport doubles the accuracy.

```lean
theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_anchor_terminal       -- X4d (RISK)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A Dd Cq : ℝ) (hA : 0 < A)
    (hD : 0 < Dd) :
    ∃ C Λ Rrad ζ₀ : ℝ, 1 ≤ C ∧ 1 ≤ Λ ∧ 0 < ζ₀ ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (H : RetainedCoreHistory P₀)
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount))
      (p₀ : CutoffParameters) (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      Rrad ≤ p₀.modelRadius → 2 ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
      ∀ {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s) (q ρ Rref : ℝ),
      0 < q → q ≤ Cq * Rref → Λ ≤ Rref → Λ ≤ Rref * t → Λ ≤ ρ * Real.sqrt Rref →
      (∀ x, q < G.flow.scalar t x →
        ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) →
      H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
      G.DerivativeBoundBefore Ctime q t → G.GradientBoundBefore Cgrad q t →
      H.EventSlabsPinched phi →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      H.TerminalNoncollapsedBefore hend G hG κ ρ t →
      ∀ z x : (H.stage (Fin.last H.eventCount)).Carrier,
        G.flow.scalar t z ≤ A * Rref →
        riemannianEDistOf (G.flow.base.metric t) z x < ENNReal.ofReal (Dd / Real.sqrt Rref) →
        G.flow.scalar t x ≤ C * Rref
```
X4d (1.5–3k lines) is applied at the slice `σₙ = tₙ + s/Rₙ < t₀ₙ` through the prefix/extension of F4.
Its event form follows by `prefixAt`, as for B3e. It is pulled to the survivor flows: the maps `f j`
are injective local isometries, so stage distance ≤ `W`-distance and the scalars are equal. It then
passes to the limit slices, giving X4a's last hypothesis. Event-time slices are avoided by choosing
`s' ∉ ⋃ₙ Eₙ` (a countable set) and using continuity of the limit scalar in `s`.

The route (F5):
1. Rebase along the sublevel path (`OrientedThreeStage.ClosedSlab.exists_rebase_chain`, B3F).
2. At the rebase point `w`:
   - if `w` is not a `CWP(D₁, 1/2)`, apply the delivered B3e (`…SliceTerminal.lean:249`) at `w`;
   - otherwise use the standard-cap window bound `R ≤ C(D₁)·λ` on `B(w, D₂/√λ)`, with `λ ≤ 2R(w)` by
     `hscale` (the cap scalar lower bound).
3. If the ball leaves the window, H9's first-touch argument applies, with `Dcap` enlarged after `C_B`.

```lean
theorem exists_subseq_windowAnchorBound_of_depthExtendable {σ : ℕ → ℕ} (hσ : StrictMono σ)  -- X4
    {Tstar : ℝ} (hT : 0 < Tstar) : ⟪K τ ŷ⟫
    (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
      (fun n => (G n).flow.scalar (t n) (y n)) σ T) →
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((K (σ (ψ i))).toHistory.stageMetric
          ((K (σ (ψ i))).toHistory.activeStage (τ (σ (ψ i)))) (τ (σ (ψ i)))) (ŷ (σ (ψ i)))
          (A / Real.sqrt ((G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))))),
      ∀ (w : Icc (0 : ℝ) (K (σ (ψ i))).toHistory.horizon),
        (w : ℝ) = t (σ (ψ i)) - T' / (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i))) →
      ∀ (hwt : w ≤ τ (σ (ψ i)))
        (Bt : BackwardPointTrace (K (σ (ψ i))).toHistory
          ((K (σ (ψ i))).toHistory.activeStage w)
          ((K (σ (ψ i))).toHistory.activeStage (τ (σ (ψ i))))
          ((K (σ (ψ i))).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((K (σ (ψ i))).toHistory.stageMetric
            ((K (σ (ψ i))).toHistory.activeStage w) w)
          (Bt.point ((K (σ (ψ i))).toHistory.activeStage w) le_rfl
            ((K (σ (ψ i))).toHistory.activeStage_mono hwt)) ≤
          M * (G (σ (ψ i))).flow.scalar (t (σ (ψ i))) (y (σ (ψ i)))
theorem depthExtendable_add_of_windowAnchorBound {σ : ℕ → ℕ} (hσ : StrictMono σ)           -- X4ext
    {Tstar M : ℝ} (hT : 0 < Tstar) (hM : 0 ≤ M) : ⟪K τ ŷ⟫
    (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable … σ T) →
    (the anchor bound of X4 along σ with this M) →
    ObservedHistory.DepthExtendable (fun n => (K n).toHistory) τ ŷ
      (fun n => (G n).flow.scalar (t n) (y n)) σ
      (Tstar + 1 / (32 * ((Ctime : ℝ) + 1) * (M + 1)))
```
**X4** (600–1100 lines of assembly) proceeds as follows:
1. W1 with `τ_k := T*(k+1)/(k+2)`, then glue on `openClosed`.
2. `Rm ≥ 0`: a window version of `AncientPointedFlowLimitCurvature.lean:26`.
3. Completeness: `complete_at_earlier_time_of_ricci_nonnegative` (`Estimates/MetricComparison.lean:470`).
4. Witnesses on every limit slice:
   - B6 `exists_neckAlternatives_of_survivor_maps` (`TracedRegionAncientLimitNeckAlternatives.lean:21`);
   - B9 `…_at_shifted_times` (`ShiftedTransfer:354`) with a strict threshold margin.
5. The derivative clause: Part A, `abs_derivWithin_scalar_le_of_local_flow_limit`
   (`AncientPointedFlowLimitTransfer.lean:283`).
6. `hRP` from X4d.
7. X4a gives `C`.
8. `M := 2(C+1)` by `C⁰` convergence at `s = −T'` on the compact ball over `B̄(A)`.
   Anchors: `Bt.point = f_j x` (`BackwardPointTrace.point_unique`).

**X4ext** (300–500 lines) is DESIGN_MAXWINDOW §4.3:
- the backward step `scalar_le_two_mul_of_backwardPointTrace_of_scalar_le_at`
  (`TracedRegionBackwardStep.lean:121`), with `Δ = 1/(8(Ctime+1)(M+1))` and gain `Δ/4`;
- then B5, whose right branch is excluded through `mono`;
- all constants of B5 are fixed per `A`, and `n` grows.

### 2.8 X5: ancient limit and the three clauses (400–700 lines of assembly on B13)
```lean
theorem ObservedHistory.exists_eventually_canonical_clauses_of_isTracedRegion :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C τ₀ : ℝ, 1 ≤ C ∧ 0 < τ₀ ∧
    ∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier) (R : ℕ → ℝ),
      (∀ n, 0 < R n) →
      (∀ n, metricScalarAt ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) = R n) →
      Tendsto R atTop atTop →
      ∀ (hlt : ∀ n, (H n).time ((H n).activeStage (t n)) < t n),
      ((∀ n, τ₀ ≤ R n * ((t n : ℝ) - (H n).time ((H n).activeStage (t n)))) ∨
        ∀ n, R n * ((t n : ℝ) - (H n).time ((H n).activeStage (t n))) < τ₀) →
      (∀ A T : ℝ, 0 < A → 0 < T → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (H n).isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n)) →
      ∀ {κ ρ : ℝ}, 0 < κ → 0 < ρ → ∀ {t₀ : ℕ → ℝ}, (∀ n, t₀ n ≤ t n) →
      Tendsto (fun n => R n * ((t n : ℝ) - t₀ n)) atTop (𝓝 0) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon) (p : ((H n).stageAt v).Carrier) (r : ℝ),
        (v : ℝ) < t₀ n → r ≤ ρ → (H n).isParabolicallyRmControlledBall v p r →
        ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt v).Carrier
            ((H n).stageMetric ((H n).activeStage v) v)
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage v) v) p r)) →
      ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) ≤ t n →
        ∀ x : ((H n).stageAt v).Carrier,
          curvatureOperatorLowerBoundAt ((H n).stageMetric ((H n).activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt ((H n).stageMetric ((H n).activeStage v) v) x)
            (Phi (metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) x))) →
      ∀ {C1s C2s Cs Cq : ℝ} {Ctime : ℝ≥0} {qs qcan : ℕ → ℝ},
      (∀ n, qs n ≤ Cs * R n) → (∀ n, qcan n ≤ Cq * R n) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
          qs n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
          ∃ W : SpatialCanonicalWitness ((H n).stageMetric ((H n).activeStage v) v) ε C1s C2s p,
            W.capTubeHasNeckChart ε) →
      (∀ n (v : Icc (0 : ℝ) (H n).horizon), (v : ℝ) < t₀ n →
        (H n).time ((H n).activeStage v) < v → ∀ p : ((H n).stageAt v).Carrier,
          qcan n < metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p →
          |derivWithin (fun v' => metricScalarAt ((H n).stageMetric ((H n).activeStage v) v') p)
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((H n).stageMetric ((H n).activeStage v) v) p ^ 2) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
        (τ₀ ≤ ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i)) (y (ψ i)) *
            ((t (ψ i) : ℝ) - (H (ψ i)).time ((H (ψ i)).activeStage (t (ψ i)))) →
          ∃ W : CanonicalWitness ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow ε C C
            (y (ψ i)) (t (ψ i)), W.capTubeHasNeckChart ε) ∧
        |derivWithin (fun v =>
            ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar v (y (ψ i)))
            (Iic (t (ψ i) : ℝ)) (t (ψ i))| ≤
          C * ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i))
            (y (ψ i)) ^ 2 ∧
        ∀ v : TangentSpace I3 (y (ψ i)),
          |Perelman.CanonicalNeighborhood.scalarDifferential
              ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow (t (ψ i)) (y (ψ i)) v| ≤
            C * ((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i)) (y (ψ i)) *
              Real.sqrt (((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.scalar (t (ψ i))
                (y (ψ i))) *
              Real.sqrt ((((H (ψ i)).closedPrefixAt (t (ψ i)) (hlt (ψ i))).flow.base.metric
                (t (ψ i))).inner (y (ψ i)) v v)
```
Proof route and constants:
- `epsW` is B11's (`ShiftedTransfer:551`). `C := max C_wit C_der` and `τ₀ := δ(ε)⁻¹ + 1`, both from
  B8 `:117/:533`.
- B13 (`TracedRegionAncientLimitScalarBound.lean:42`, in progress) gives, on the κ-before-`t₀`
  variant (TimeControl:781):
  - the bounded ancient limit;
  - its κ at every scale (`κ/250`, already in TimeControl's conclusion).
- `ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete` (`AncientPointedFlowLimitCurvature.lean:122`)
  and `isAncientKappaSolution_flowOfMetric_of_curvatureOperator_nonnegative` (`:185`) give
  `IsAncientKappaSolution (κ/(250·30³))`.
- X5d gives the base scalar `= 1`, and X5c the orientation (stages are `OrientedThreeStage`).
- B8 (2)(3)(4) are applied with `S n := closedPrefixAt`, `D n := closed a (t n)`, and `(X.obj n)`
  from B6b′.
- `hmode` selects B8 (2) or makes the witness clause vacuous.

The Crossing supply of X5, on `Kₙ = extendAt`:

| X5 input | Supply |
|---|---|
| `hwit` | `EventSlabsSpatiallyCanonical` together with `SpatiallyCanonicalBefore t₀`, through a stage bridge (small, shaped like B6B3 lemma 4) |
| `hderiv` | B12 `abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt` (`TracedRegionAncientLimitDerivativeCutoff.lean:86`) |
| `hnc` | `TerminalNoncollapsedBefore` through `noncollapsedBefore_closedPrefix_of_terminalNoncollapsedBefore` (`BoundedCurvatureAtDistanceLimit.lean:393`), plus agreement of `extendAt t` and `extendAt v` below `v` |
| `hpinch` | `EventSlabsPinched` and `PhiAlmostNonnegative` |
| `hsliver` | the context |
| `htraced` | X2 in the infinite case |
| `Cq` | 1 |

```lean
theorem nonempty_tangentOrientationSection_of_pointedConvergence                    -- X5c, 150–300
    {X : PointedRiemannianSeq.{u, 0, 0} I3} {P : PointedRiemannianManifold.{u, 0, 0} I3}
    {f : ℕ → ℕ} (F : PointedRiemannianConvergenceMaps X P f)
    (o : ∀ n, TangentOrientationSection (X.obj n).M) (hPc : MetricComplete P)
    [ConnectedSpace P.M] {V : ℕ → Opens P.M}
    (hV : ∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2))
    {N : ℕ → ℕ} (hVF : ∀ k j, N k ≤ j → (V k : Set P.M) ⊆ F.source j) :
    Nonempty (TangentOrientationSection P.M)
theorem metricScalarAt_basepoint_eq_of_local_flow_limit                              -- X5d, 50–100
    … (B6b′'s F, V, hV, φ, hφF, G, hG0, ψ, hconv) …
    (hW0 : ∀ k, ∀ᶠ n in atTop, ∀ z : W k n,
      metricScalarAt (h k n 0) z = metricScalarAt (X.obj n).metric z)
    {c : ℝ} (hbase : ∀ n, metricScalarAt (X.obj n).metric (X.obj n).basepoint = c) :
    metricScalarAt P.metric P.basepoint = c
```
Proofs:
- X5c:
  - pull back `o (f j)` along `F.partialDiffeomorph j` onto each connected `V k`, using
    `TangentOrientationSection.pullback` (`Perelman/CanonicalNeighborhood/WindowedModelLocalPull.lean:111`);
  - fix the signs inductively along `V k ⊆ V (k+1)` (the private `negOrientation` /
    `isOpen_setOf_orientation_eq` pattern, `StandardClosenessEndpointWitness.lean:35`).
- X5d: pointwise scalar convergence at the basepoint.

### 2.9 X6: the κ-solution gives the canonical neighbourhood, pulled back

No new classification is needed. The existing chain is:
- the κ-solution canonical neighbourhood `kappa_canonical_neighborhood` (`AncientCanonicalNeighborhood.lean`),
  as consumed through `exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness`
  (`Perelman/CanonicalNeighborhood/WindowedModelCanonicalWitness.lean:22`, which covers the
  round and non-round branches, hence also compact limits (old F8));
- inside `exists_canonicalWitness_of_ancient_pointed_flow_limit` (`AncientLimitCanonicalWitness.lean:117`),
  `eventually_scalar_derivative_bounds_of_ancient_pointed_flow_limit` (`:533`) and
  `canonical_bounds_of_canonicalWitness_of_scalar_derivative_bounds` (`:29`).

The only new piece is the transport back to `G.flow` together with the constant upgrade
(X6b, 100–200 lines):
```lean
theorem RetainedCoreHistory.canonical_clauses_of_extendAt (H) (hend) (G) (hG) {t} (hat) (hts)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (ŷ : ((H.extendAt hend G hG hat hts).toHistory.stageAt
      (H.extendAtTime hend G hG hat hts)).Carrier) (hy : HEq ŷ y)
    (hlt : (H.extendAt hend G hG hat hts).toHistory.time
      ((H.extendAt hend G hG hat hts).toHistory.activeStage (H.extendAtTime hend G hG hat hts)) <
        (H.extendAtTime hend G hG hat hts : ℝ))
    {ε C C1 C2 τ₀ τmin : ℝ} {Ctime Cgrad : ℝ≥0} (h1 : C ≤ C1) (h2 : C ≤ C2)
    (h3 : C ≤ Ctime) (h4 : C ≤ Cgrad) (hτ : τ₀ ≤ τmin) :
    (τ₀ ≤ S.scalar t ŷ * (t - a) → ∃ W : CanonicalWitness S ε C C ŷ t, W.capTubeHasNeckChart ε) →
    |derivWithin (fun v => S.scalar v ŷ) (Iic t) t| ≤ C * S.scalar t ŷ ^ 2 →
    (∀ v, |scalarDifferential S t ŷ v| ≤ C * S.scalar t ŷ * √(S.scalar t ŷ) * √(g_t(v,v))) →
    (τmin ≤ G.flow.scalar t y * (t - H.time (Fin.last H.eventCount)) →
        ∃ W : CanonicalWitness G.flow ε C1 C2 y t, W.capTubeHasNeckChart ε) ∧
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
          Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
            Real.sqrt ((G.flow.base.metric t).inner y v v)
```
Here `S := ((H.extendAt …).toHistory.closedPrefixAt (H.extendAtTime …) hlt).flow` and
`a := (H.extendAt …).toHistory.time (activeStage …)`; the elaborated text spells both out.

The proof:
1. `activeStage = last` (`activeStage_extendHorizon_eq_last`, `TracedRegion.lean:648`), then
   generalize and `subst`.
2. `S` and `G.flow` agree on `Icc a t`.
3. Witnesses on `Icc (t − C2/R) t ⊆ [a, t]` transfer; `derivWithin (Iic t)` depends only on `[a, t]`.
4. `canonical_bounds_of_canonicalWitness_of_scalar_derivative_bounds`.

### 2.10 X7: the leaf, `theorem crossingContinuation (P₀) (g₀) : CrossingContinuation P₀ g₀` (300–500 lines)

It discharges:
- every hypothesis of X0–X6 from the leaf binders, as tabulated in §1, §2.3 and §2.8;
- `hext` from F9;
- the choice of `η` in the order fixed by H8: `Hₙ, t₀ₙ` first, then BS4's `S`, then `η` (inside X1),
  then the bad point.

The proof is by contradiction on the tail after `θ`:
1. X1 (with X1e for event slabs) gives `Σ`.
2. Split by age mode (F1).
3. X2 with `E σ T := DepthExtendable (K ∘ ·)`: `hdown`, `hsub` and `htail` are
   `mono_depth`, `comp` and `congr`.
4. The finite case: X4, then X4ext, give `E (σ∞ ∘ ψ) (T* + Δ)`, contradicting maximality with `χ := ψ`.
5. The infinite case: X5 on `K ∘ σ∞`, then X6b per `i`, contradict `hfail`.

## 3. Suppliers, bricks and order

Delivered suppliers are cited at `file:line` in §0–§2. The table covers what is new.

| Brick | File (new unless noted) | Lines | Depends on |
|---|---|---|---|
| X0 | `Surgery/Topology/InitialWindowScalarBound.lean` | 80–150 | HistoryCurvatureTimeBound:61, InitialSlabUniformBounds:21, HamiltonIveyPinching:666 |
| X1 | `Surgery/Topology/CrossingBadPoint.lean` | 120–200 | BS1, sliver comparison, BS4 |
| X1e | `RetainedCoreHistoryPrefixTransport.lean` additions (new file) | 80–150 | prefixAt |
| X1k | `Surgery/Topology/RetainedCoreHistoryExtendAt.lean` | 150–300 | extendHorizon, records transport |
| X2 | `Topology/Sequences/NestedSubsequence.lean` + `Surgery/Topology/TracedRegionMaximalDepth.lean` | 150–300 | `isTracedRegion.mono_depth` (`TracedRegion.lean:134`) |
| X3p | `Surgery/Topology/CrossingBaseSliceBound.lean` | 150–250 | BS5-terminal, BS6, BS3, X0 |
| W1 | next to TimeControl (after merge) | 600–1000 | TimeControl's privates (`open private`) |
| X3a + X3 | `Surgery/Topology/CrossingTimeZeroBound.lean` | 400–700 | W1, per-`k` B9 copy-edit, Transfer:440, B5, the B7 step |
| X4a + far field | `Perelman/CanonicalNeighborhood/WindowScalarBound.lean`, `SpatialFarField.lean` | 1.2–2.1k | TerminalScalar:173, BackwardScalarExterior:89 (port) |
| **X4d** | `Surgery/Topology/BoundedCurvatureAtDistanceAnchor.lean` | **1.5–3k (risk)** | B3e, rebase chain, CapWindowStandardComparison:20, H9 first touch |
| X4 | `Surgery/Topology/CrossingMaximalWindow.lean` | 600–1100 | W1, openClosed gluing (AncientGluing:17 generalization), B6, B9, Part A, X4a, X4d |
| X4ext | same file | 300–500 | TracedRegionBackwardStep:121, B5 |
| X5 | `Surgery/Topology/CrossingAncientLimit.lean` | 400–700 | B13, TimeControl:781, Curvature:122/185, B8, X5c, X5d |
| X5c, X5d | `Compactness/Limits/PointedLimitOrientation.lean` (+X5d next to B6d) | 200–400 | pullback orientation |
| X6b | `Surgery/Topology/CrossingClauseTransport.lean` | 100–200 | closedPrefixAt, B8:29 |
| X7 | `Surgery/Topology/CrossingContinuationLeaf.lean` | 300–500 | all of the above |

The total is about 6.5–11.5k lines, of which X4d accounts for 1.5–3k.

Order:
1. Now, in parallel: X0, X1, X1e, X1k, X2, W1, X4a with its far-field port, X5c, X5d, X6b.
2. X4d goes to review (§4) before its proof lane.
3. Then X3p, then X3a and X3; in parallel X4 (after W1, X4a and X4d) and X4ext.
4. X5 after B13.
5. X7 last.

## 4. Single-statement review prompt (X4, with X4d as its engine)

> 背景：Lean 4/Mathlib 中带手术的三维 Ricci 流。
>
> **序列与记号。**
> - 反证序列：`Hₙ` 为 cutoff 类历史，续接片 `Gₙ` 在 `[aₙ, sₙ)` 上，坏点为 `(yₙ, tₙ)`。
> - 已知条件：
>   - `Rₙ = R(tₙ, yₙ) → ∞`，`Rₙtₙ → ∞`，`Rₙ(tₙ − t₀ₙ) → 0`；
>   - 在 `t₀ₙ` 之前的所有切片上：阈值 `qsₙ ≤ Cs·Rₙ` 以上处处有空间典范见证（精度 `ε`），
>     导数界与梯度界成立，`κ` 非塌缩；
>   - `¬CapWindowPoint(yₙ, tₙ, Dₙ, θcapₙ)`，其中 `Dₙ → ∞`，`θcapₙ ↑ 1`。
> - `DepthExtendable σ T` 指：对每个 `A`，沿 `σ` 最终 `B(yₙ, A/√Rₙ)` 的所有点都能回溯到深度
>   `T/Rₙ`，且沿迹 `|Rm| ≤ K(A)·Rₙ`。
>
> **断言（X4）。** 若对所有 `T < T*` 均有 `DepthExtendable σ T`，则存在子列 `ψ` 与常数 `M`，
> `M` 不依赖于 `A` 与 `T'`，使得对所有 `T' < T*` 与 `A`，最终 `B(yₙ, A/√Rₙ)` 中每点在时刻
> `tₙ − T'/Rₙ` 的迹点满足 `R ≤ M·Rₙ`。
>
> **证明路线。**
> 1. 用带深度表的存活流极限（W1，`τ_k = T*(k+1)/(k+2)`），粘合成 `(−T*, 0]` 上的流。
> 2. 该极限流满足：`Rm ≥ 0`，各切片完备，阈值以上有见证（严格余量），导数条款成立。
> 3. 零时刻的整片界 `Q₀`。
> 4. 自举（X4a）：
>    - 在 `[a, 0]` 上用 Hamilton 距离比较，常数为 `(20/3)√(2T*Q₀)√T*`；
>    - 远场界；
>    - 锚定 hRP：`R(z,s) ≤ A`，`d_s(z,x) ≤ D` ⇒ `R(x,s) ≤ C(A,D)`，对 `s` 一致；
>    - 导数步长。
>    这样得到 `(−T*, 0]` 上的一致界 `C`，于是 `M = 2(C+1)`。
> 5. 锚定 hRP 来自 X4d：在 `t₀` 之前的切片上，对任意锚点作有界距离的曲率界，**不假设** ¬CWP。
>    重基点若非 CWP，用已证的 B3e；若是年轻帽窗点，用标准解窗口的曲率可比性（`λ ≤ 2R(w)`），
>    越出窗口时用 H9 的首次接触论证。
>
> **请检查：**
> - (a) X4d 是否为真。尤其是年轻帽（年龄 `≤ 1/2`）内曲率在有界归一化距离上与 `λ` 可比，
>   是否对标准解一致成立；以及在窗口内之后发生的手术（尺度与 `Rₙ` 可比）是否会破坏该论证。
> - (b) hRP 为何不能以基点为中心：`R(p, s)` 仅有 Harnack 率 `T*Q₀/(s+T*)`。并请检查是否存在
>   更弱的、可供给的替代条件。
> - (c) 常数与量词：`C(A,D)` 须对 `s ∈ (−T*, 0)` 一致；`n₀` 可依赖于 `s`；事件时刻切片用可数
>   例外集回避。
> - (d) W1 把深度改为 `τ_k`（而非 `2τ_k`）以及内窗 `(k+1)/(k+2)·τ_k` 是否足够给出 Shi 导数界、
>   κ 检验与收敛。
> - (e) 能否构造反例：有界 `T*`，但极限在 `−T*` 附近曲率无界，而上述所有假设都成立。
