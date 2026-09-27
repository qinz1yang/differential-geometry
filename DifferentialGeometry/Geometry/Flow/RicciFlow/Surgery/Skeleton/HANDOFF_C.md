# Leaf C, decomposed: pinching (proved), noncollapsing, continuation

Statement: `Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean`,
`def CanonicalNeighborhoodsThroughSurgery`. Decomposition and assembly:
`Surgery/Topology/CanonicalNeighborhoodInduction.lean`
(`canonicalNeighborhoodsThroughSurgery_of_continuation_of_noncollapsing_of_pinching`, proved).
C1 is proved (`Surgery/Topology/PinchingThroughSurgery.lean`, `pinchingThroughSurgery`). Leaves:
`Surgery/Skeleton/PoincareEndgame.lean`, `noncollapsingThroughSurgery`,
`canonicalNeighborhoodContinuation`. Ledger: `Surgery/FREE_INPUTS.md`. Review record:
`Surgery/consult/A-poincare-endgame-first-review-digest.md` (2026-09-25).

## Skeleton path since 2026-09-26: the strong interface

The skeleton consumes `CanonicalNeighborhoodsThroughSurgeryStrong`
(`Surgery/Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean`), assembled by
`canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` from C1 `pinchingThroughSurgery` (proved), C2
`noncollapsingThroughSurgery_of_reducedVolume_of_smallScale` on its four leaves, C3
`canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing` with C3a `deepContinuation`
proved (`Surgery/Topology/DeepContinuation.lean`) and C3b/C3c leaves, and C4
`SpatialCanonicalContinuation` (leaf `spatialCanonicalContinuation`). The endpoint is
`smoothPoincareConjecture_of_uniformDebitSurgeryStepStrong_of_canonicalNeighborhoodsStrong` with S
the leaf `uniformDebitSurgeryStepStrong`. The strong C also outputs the gradient clause, the spatial
clause, the initial pinching `a₀`, and `κ` with `TerminalNoncollapsedBefore`, and takes
`p₀.recenterConstant ≤ Λ` (item 8 below is realised there). The old `CanonicalNeighborhoodsThroughSurgery`
described below is weaker (its clauses minus the recenter constraint are the projection `canonicalNeighborhoodsThroughSurgeryOfRecenter_of_strong`) and is no longer on the skeleton path.

C4 interface (I28c, accepted by ACC5): both branches of `SpatialCanonicalContinuation` (event slab
and terminal slab) now take, after the noncollapsing hypothesis, C3's own output on the same slab,
`∃ η > 0, DerivativeBoundOn Ctime qcan t₀ η ∧ GradientBoundOn Cgrad qcan t₀ η ∧
CanonicalOn ε C1 C2 qcan τmin t₀ η`, verbatim from `CanonicalNeighborhoodContinuation`'s
conclusion (`DESIGN_C4.md` failure 1). The strong assembly obtains it from the C3 leaf (`hF'`) at the
same `t₀` and passes it both to the combiner and to the C4 leaf, so C4 is proved knowing that the
age-restricted canonical, derivative and gradient clauses already continue past `t₀`; it still
concludes only `SpatiallyCanonicalOn` on its own `[t₀, t₀ + η)`. `PoincareEndgame` is unchanged
(the leaf names the predicate).

## Binder order after the interface revision (entry 28, accepted 2026-09-26)

C is now an `∃ εbar` statement whose body is `CanonicalNeighborhoodsThroughSurgeryStrongAt`
(`Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean:69` and `:24`); the constants
`C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap mcap Ctime Cgrad κ a₀` are chosen after `B ε Λ`, and
the class is `InCutoffClass` with the new last conjunct `p₀.recenterConstant * δbound ≤ 1 / 2`
(from `p₀.recenterConstant ≤ Λ`, `CutoffParameters.recenterConstant_mul_le_half`). C3 and C3c also
begin `∃ εbar`; C4 outputs `C1s C2s Cs` before `κ` and a floor `q₄` after `κ phi`, with
`qcan ≤ qs ≤ Cs * qcan`; C3 takes `C1s C2s Cs` and `∀ qfloor` and returns `qfloor ≤ qcan`. The old
assembly `canonicalNeighborhoodsThroughSurgery_of_continuation_of_noncollapsing_of_pinching` is
deleted.

```lean
def CanonicalNeighborhoodsThroughSurgeryStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    Prop :=
  ∃ εbar : ℝ, 0 < εbar ∧
  ∀ (B ε Λ : ℝ), 0 < B → 0 < ε → ε < 1 / 11 → ε ≤ εbar → 0 < Λ →
    CanonicalNeighborhoodsThroughSurgeryStrongAt P₀ g₀ B ε Λ

def CanonicalNeighborhoodsThroughSurgeryStrongAt (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) (B ε Λ : ℝ) : Prop :=
  ∃ (C1 C2 C1s C2s qcan τmin δmax ρmax εcap Dcap : ℝ) (mcap : ℕ) (Ctime Cgrad : ℝ≥0)
    (κ a₀ : ℝ),
    1 ≤ C1 ∧ 1 ≤ C2 ∧ 1 ≤ C1s ∧ 1 ≤ C2s ∧ 0 < qcan ∧ 0 < τmin ∧ 0 < δmax ∧ 0 < ρmax ∧
    0 < εcap ∧ 0 < Dcap ∧ 0 < κ ∧ 0 < a₀ ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      ...
```

## What C says (after the 2026-09-25 repair)

For every horizon `B > 0` and accuracy `0 < ε < 1/11` there are constants `C1 C2 ≥ 1`, a threshold
`qcan > 0`, a normalized age `τmin > 0`, a derivative constant `Ctime`, admissibility bounds
`δmax ρmax εcap > 0`, a cap window radius `Dcap > 0` and a cap model order `mcap` such that for
every cap parameter set `p₀` with `p₀.modelAccuracy ≤ εcap`, `Dcap ≤ p₀.modelRadius`,
`mcap ≤ p₀.modelOrder`, every `δbound ≤ δmax`, `ρbound ≤ ρmax`, and every history `H` with
`H.hasCanonicalCutoffRecords p₀ δbound ρbound` (initial identification from `(P₀, g₀)`,
`H.time last = H.horizon < B`):

* on every event slab, at every point with `qcan < R`: `|∂ₜ⁻R| ≤ Ctime R²`;
* for every singular incoming slab `G` from the last stage with `s ≤ B` and compatible initial
  metric: the same derivative bound, and at every `(x, t)` with `t ∈ (a, s)`, `qcan < R` and
  `τmin ≤ R · (t − a)` a witness `W : CanonicalWitness G.flow ε C1 C2 x t` with
  `W.capTubeHasNeckChart ε`.

The age restriction is forced by the tree: both alternatives of `CanonicalWitness` contain a
`StrongNeck`, whose backward window `[t − R⁻¹, t]` must lie in the slab
(`StrongNeck.sub_inv_scalar_mem_carrier`, `PartialStandardSolution.isEmpty_canonicalWitness_of_time_mul_scalar_lt`
in `Surgery/Topology/StandardCapCanonicalTransport.lean`). Fresh cap points (`R ≈ h⁻²`,
`t − a ≪ h²`) have no witness. Kleiner–Lott's ε-cap needs only a spatial neck; the tree's cap is
stronger, so the clause is restricted instead. The derivative clause is not restricted: in the fresh
layer it comes from the standard-solution comparison, which consumes exactly this clause.

## Vocabulary (`CanonicalNeighborhoodInduction.lean`)

* `G.CanonicalBefore ε C1 C2 qcan τmin t₀`: witnesses with cap–neck charts at every point of the
  slab with time in `(a, t₀)`, `qcan < R`, `τmin ≤ R (t − a)`. `G.DerivativeBoundBefore Ctime qcan t₀`:
  the derivative bound before `t₀`. `G.CanonicalOn … t₀ η`, `G.DerivativeBoundOn … t₀ η`: the same on
  `[t₀, t₀ + η) ∩ (a, s)`.
* `H.NoncollapsedBefore κ ρ t₀` (history-wide, parabolic): every
  `H.toHistory.isParabolicallyRmControlledBall t p r` (`HistoryParabolicBall.lean`: the ball at time
  `t` whose points trace back regularly through the retained cores over `[t − r², t]` with
  `r⁴|Rm|² ≤ 1` along the traces) with `t ≤ t₀`, `r ≤ ρ` has volume `≥ κ r³`.
* `H.TerminalNoncollapsedBefore hend G hG κ ρ t₀`: for every `T ∈ (a, s)`, `T ≤ t₀`, the history
  `H.extendHorizon T … (G.closedPrefix T …)` is `NoncollapsedBefore κ ρ T`. This attaches the
  terminal slab to the history so that balls whose window crosses the last surgery time are
  covered; balls meeting a fresh cap have no backward trace and are outside the predicate.
* `H.EventSlabsPinched phi`, `H.EventSlabsCanonical ε C1 C2 qcan τmin k`,
  `H.EventSlabsDerivative Ctime qcan k`: all event slabs pinched; the event slabs `j.castSucc < k`
  canonical (age-restricted) and derivative-bounded up to their end times.
* `H.InCutoffClass g₀ B p₀ δbound ρbound`, `H.IsContinuationSlab B k G` as before.

Each of C2 and C3 has two clauses: (E) for an event slab `j` of the class history, whose
noncollapsing is `H.NoncollapsedBefore`, and (T) for the terminal singular slab, whose
noncollapsing is `H.TerminalNoncollapsedBefore` together with `H.NoncollapsedBefore … (H.time last)`.

## C2 `NoncollapsingThroughSurgery` (Perelman II 5.2, KL 78–80)

`∀ B ε C1 C2 τmin Ctime phi, ∃ κ > 0, ∀ qcan > 0, ∃ δmax ρmax εcap Dcap mcap, ∀ admissible p₀ δbound ρbound,
∀ H ∈ class, all event slabs pinched → (E) ∧ (T)` where
(E): for every event slab `j`, if the earlier event slabs are canonical and derivative-bounded up
to their ends and slab `j` is canonical and derivative-bounded before `t₀ ∈ (time j, time (j+1)]`,
then `H.NoncollapsedBefore κ ε t₀`; (T): the same for the terminal slab with `t₀ ∈ (a, s)` and the
conclusion `H.TerminalNoncollapsedBefore … κ ε t₀`.

`κ` is chosen before `qcan`; the admissibility bounds after. Perelman's proof runs the reduced
volume from `(x, t₀)` back to time `0` through the whole history; curves through the surgery caps
have large action (the collaborator's `HistoryAction`, `CapWindowAction` and the history parabolic
balls on `origin/codex/wt17-pc-build-warning` are this material), so `κ` depends on `(P₀, g₀, B, ε)`
only. The initial short time interval on which the flow from `g₀` has bounded curvature is part of
the proof (external review, item 3; Lane O). Balls at the end time `time (j+1)` in the new stage are
only those whose points trace back through the retained core; this is what makes
`H.NoncollapsedBefore κ ε (time (j+1))` available to the next slab.

## C3 `CanonicalNeighborhoodContinuation` (Perelman II 5.1 first failure, KL 77.2, 79)

`∀ B ε, ∃ C1 C2 τmin Ctime, ∀ κ phi, ∃ qcan δmax ρmax εcap Dcap mcap, ∀ admissible, ∀ H ∈ class, pinched →
(E) ∧ (T)` where (E): for an event slab `j` with earlier slabs canonical and derivative-bounded, if
slab `j` is canonical and derivative-bounded before `t₀ ∈ [time j, time (j+1))` and
`H.NoncollapsedBefore κ ε t₀`, then `∃ η > 0` with the derivative bound and the age-restricted
witnesses on `[t₀, t₀ + η)`; (T): the same for the terminal slab, from
`H.NoncollapsedBefore κ ε (H.time last)` and `H.TerminalNoncollapsedBefore … t₀`.

### Status 2026-09-26 (ACC7)

C3a `deepContinuation` and C3b `capWindowContinuation` are PROVED
(`Topology/DeepContinuation.lean`, `Topology/CapWindowContinuationLeaf.lean`: the slab-interior
theorem plus `RetainedCoreHistory.exists_slice_bounds_at_slab_start` from
`Topology/SlabStartDerivativeBounds.lean`). Only C3c `crossingContinuation` remains in C3.
`CrossingContinuation` binder order (lane M6): `∃ Dcap θcap q₀ mcap, 0 < Dcap ∧ θcap < 1 ∧ 0 < q₀ ∧
∀ qcan ≥ q₀, ∃ δmax ρmax εcap > 0, ∀ qs ∈ [qcan, Cs·qcan], …`, the same order as
`CapWindowContinuation`; `Dcap θcap mcap` stay before `qcan` because the cap leaf consumes them
before its own `qcan`; `ρmax` may depend on `qcan` (B5 needs `ρmax² ≤ min (Cbirth/(4 qcan)) (a₀/2)`
with `Cbirth` fixed from `Ctime` before `Θ`, `OPUS_FILL_LOG_M6.md`).

### Status 2026-09-26 (ACC8)

C3c inputs accepted, none closes the leaf. B3e holds on both slabs: on the terminal slab
`RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal`
(`Topology/BoundedCurvatureAtDistanceSliceTerminal.lean`) and on an event slab `…_event`
(`BoundedCurvatureAtDistanceSliceEvent.lean`, through the prefix history `H.prefixAt j.castSucc`,
`RetainedCoreHistoryPrefix{,Transport}.lean`), each with an `eventually_…` sequence form. Base-slice
inputs: the witnesses at `t`, `¬CapWindowPoint`, noncollapsing up to and including `t`, pinching;
the derivative and gradient clauses only on `Ioo a t` (`OPUS_FILL_LOG_B3F.md`, flag F-g). The
rebased form for `hRP` (¬`CapWindowPoint` at the recentre point) is OPEN. B6d's limit-level
transfer (`AncientPointedFlowLimitTransfer.lean`) is proved with the hypothesis `hEreg`, which the
history consumer cannot meet at slice times exceptional for infinitely many `n`; B11 of
`DESIGN_B6D_GLUE.md` restates it. B6b'' (`TracedRegionAncientLimitWitnesses.lean`) and the glue
bricks B1–B3/B12 are accepted; B4–B7, NC0, X and BASESLICE are running.

### Status 2026-09-26 (ACC9)

C3c inputs accepted, none closes the leaf. Base slice (`DESIGN_BASESLICE.md`): BS1–BS5 and BS7
(`SlabTimeWindowContinuity`, `SliverWindowData`, `CapWindowPointTimeSlack`, `SliceBallBoundTransfer`,
`BoundedCurvatureAtDistanceSliver` event and terminal, `InitialSlabScalarWindow`); BS6 (ball bound at
a post-surgery stage start) is running. B6d glue B4–B6 (`Metric/Pullback/LocalDistance`,
`NeckAlternativesLocalPull`, `TracedRegionAncientLimitNeckAlternatives`: the neck alternatives `hW`
from the survivor maps) accepted; B7 delivered, its κ-variant running; B11 open. NC0
(`Perelman/Noncollapsing/TerminalTime`) gives κ-noncollapsing at the terminal time of the limit.

### Status 2026-09-26 (ACC10)

C3c inputs accepted, none closes the leaf. Base slice: BS6 (post-surgery stage start,
`BoundedCurvatureAtDistanceAfterEvent`) accepted, so BS1–BS7 are DONE. B6d glue: B7 (lane B6G3: uniform
time-Lipschitz bounds, the B6b′ limit with time control and κ only before the sliver,
`TracedRegionAncientLimitTimeControl`, `AncientPointedFlowLimitTerminalNoncollapsing`) and B8–B11 (lane
B6G4: `AncientPointedFlowLimitShiftedTransfer`, restated B6d headline) accepted, so glue B1–B12 are DONE;
B13 (composed) and the Crossing assembly design are running. C2: C9 (`CoreIntegralBound`) DONE, M
running, T9/H7b+/SB3/H8/H9 pending; small-scale S1–S4/S4′/R0–R4 DONE, S0/S6/S7 and the leaf running.
C4: G, M2 (corrected shape: comparison set with closure in the window), M3 (universe-general
pushforward) DONE; M1a/M1b/M4/M4★ running.

### Status 2026-09-26 (ACC11)

None closes a leaf. C3c: B13 composed headline accepted
(`TracedRegionAncientLimitScalarBound`, `exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`),
so glue B1–B13 are DONE; the assembly design `DESIGN_CROSSING_ASSEMBLY.md` (X0–X7, W1) is DONE, X4d is under
review H14, lane XA1 (X0/X2/X5c/X5d) is running. C2: M (lane C2M: `CostSemicontinuity`, `CurveAction`,
`MinDomainMeasurable`) DONE; H7b finishing; H7b+/T9/SB3/H8/H9 pending; small-scale S0/S6/S7 and the leaf
running. C4 (B): M1a/M1b/M4/M4★ (lane C4B2) accepted, so M1a/M1b/M2/M3/M4/M4★/G are DONE; M5 running.
CP1 (the collaborator's ball-volume bounds as new files) was dropped from ACC11: the owner ordered the
full cherry-pick of the collaborator's commits (entry 23) instead.

### Quantifier order (kept; decided 2026-09-25 evening)

`τmin` stays a model constant chosen with `C1 C2 Ctime` before `κ`. An attempt to choose `τmin` after
`κ` (so that `τmin ≥ 2θ(κ)` would make every witness deep inside its slab) was reverted the same
evening: the derivative clause is unrestricted and `Ctime` precedes `κ`, and at young unscathed
points (old points of an untouched component, made young by a cut elsewhere) it needs bounded
curvature at bounded distance, i.e. canonical structure in the young layer, i.e. the crossing
blow-up; the reorder only moved that machinery from the witness clause to the derivative clause.
Second review: `consult/B-poincare-endgame-second-review-digest.md`. Points of age in
`[τmin, θ(κ))` go through the crossing (common flow) or the standard-cap branch.

Two facts about the deep-inside machinery (Lane L, 2026-09-25):

* `UniformKappaCanonicalThreshold.lean:224-262` only uses noncollapsing of balls with
  `r² ≤ θ/R` at times in `[t − θ/R, t]` (its `hncAux` at scale `rho` is rescaled by `A = R/θ` and
  cut to normalized scale `1`); the hypothesis can be weakened to that time/scale-local form
  mechanically, and `SlabContinuationDeepInside.lean:117-170` adapted to the bridge-shaped
  hypothesis (`a ≤ τ − r²`).
* Residual gap: the model theorem's `ClosedModelHypotheses.noncollapse` is SPATIAL
  (`SpatiallyKappaNoncollapsedBelowScale S3 kappa 1`) at every centre, i.e. at curvature scale
  `R/θ`, while the bridge `SlabSpatialNoncollapsingBridge.lean:106` converts parabolic to spatial
  only under `qcan r² < 9` (curvature scale `≳ qcan/9`); bad points with `R ∈ (qcan, 9 qcan θ)` are
  not covered. Perelman's hypothesis is parabolic. The refactor of the machinery to a parabolic
  `noncollapse` field (global in space, so recentering is unaffected) is being assessed.

### Proof plan and the bricks (the reviewer's contracts, adjusted to the lane deliveries)

Suppose the conclusion fails for the class: take `qcan_n → ∞`, bounds `→ 0`, histories `H_n`,
slabs, times `T_n := t₀` and, for every `η`, bad points in `[T_n, T_n + η)`.

1. **Point picking with vanishing normalized age** (Lane P delivered; the two-stage corollary is
   Lane W's brick 1). `IncomingSlab.exists_noncanonical_point_with_canonical_above_double` with
   `η = 1/n` gives `Q₁`; applied again with `η' = min (1/n) (β_n / (2 Q₁))` the second bad point lies
   in the first window, so `Q₂ < 2 Q₁` and `Q₂ (t₂ − T_n) < β_n`; every point at a time `≤ t₂` with
   `R ≥ 2 Q₂` is canonical (before `T_n` by `CanonicalBefore`, after by the picking). Choose `β_n → 0`.
2. **Fixed-scale backward control** (Lane B, delivered):
   `IncomingSlab.scalar_le_on_backward_cylinder_of_canonicalWitness` gives `R ≤ 8Q` on the ball of
   radius `c(C2)/√(2Q)` at time `t'` and times `[t' − c(C2)/(2Q), t']`, when that window lies in the
   slab; `sqrt_rmNormSq_le_on_backward_cylinder_of_canonicalWitness` adds pinching for `|Rm|`.
3. **Deep inside the slab** (Lane U, delivered; Lane V bridge and Lane W assembly in progress):
   `IncomingSlab.exists_uniform_canonical_threshold_of_spatially_noncollapsed`: with `Q₀(ε, κ, ρ, Phi) ≤ R`,
   a backward window `θ/R` inside the slab, pinching on it and SPATIAL κ-noncollapsing of all balls
   of radius `≤ ρ` at the times of the window, the point has the witness with the `ε`-only constant.
   Point picking and bounded curvature at bounded distance are inside the machinery. Glue: the
   bridge from the parabolic history noncollapsing (`H.NoncollapsedBefore`, plus
   `ForwardTransfer.lean` for the times in `(T_n, t_n]` where `Q (t_n − T_n) → 0`) to the spatial
   hypothesis at scales `≤ ρ`, using the derivative bound above `qcan` and the curvature bound of
   step 2 on the short window.
   Glue delivered (Lane G, `Surgery/Topology/HistoryNoncollapsingToSlab.lean`):
   `RetainedCoreHistory.isKappaNoncollapsed_of_noncollapsedBefore` and
   `…_of_terminalNoncollapsedBefore` turn `H.NoncollapsedBefore κ ρ t₀` (resp. the terminal
   predicate) into the bridge's slab hypothesis for every ball whose window lies in the slab
   (`0 < κ` is needed because `IsKappaNoncollapsed` contains it). `activeStage` takes the new stage
   at an event time, so a window ending exactly at the slab start needs no limiting argument.
4. **Crossing the last surgery time unscathed** (open; the largest brick). Points of age in
   `[τmin, θ(κ))` whose window `θ/R` reaches below `a` through the retained core: the history
   parabolic ball provides a common flow across the events
   (`ObservedHistory.exists_common_flow_of_parabolicallyRmControlledBall`, `wt17` only; the base tree
   has `HistoryParabolicBall.lean` with the ball predicate). The blow-up must run on a local flow on a
   ball, which the compact-manifold machinery does not cover (Lane L: incomplete-source pointed
   compactness is absent; localizing `NormalizedSequence` costs 1.5–3k lines). Lane C delivered the
   dichotomy `GeometricCutoffRecord.exists_regularCrossing_or_exists_cap` (a point of the new stage
   without a regular crossing lies in a retained cap, `Surgery/Topology/EventCapCapture.lean`) and
   `ObservedHistory.exists_cap_capture` (latest event without a crossing, window coordinates of the
   capture point, needs canonical windows). Short-time scalar control along a backward trace
   (`R(γ(v), v) ≤ 2M` on `[u, t]` when `Ctime M (t − u) ≤ 1/2`, review FIX 1) is the next brick.
5. **Scathed: capture and standard-cap stability** (open on this lineage). Needed: (a) capture
   (Lane C, above); (b) the cap is `Cᵐ`-`η`-close to the standard solution up to normalized age
   `θ_cap < 1` using only the derivative bounds (the collaborator's
   `ObservedHistory.exists_uniform_standard_cap_comparison_of_normalized_age_bound` on
   `origin/codex/wt17-pc-build-warning` consumes exactly the derivative clause; `pc2` worktree);
   (c) the standard solution has witnesses wherever `τmin ≤ t · R`
   (`PartialStandardSolution.exists_canonicalWitness_with_cap_neck_charts_of_age`,
   `Perelman/StandardSolution/CanonicalWitnessPositiveAge.lean`, Lane X); (d) a `MetricComparisonOn`
   with time jets from spatial `Cᵖ`-closeness on a window `Icc c b`, `a < c`
   (`exists_metricComparisonOn_of_uniform_metricDerivNorm_lt`,
   `Perelman/CanonicalNeighborhood/SpatialClosenessTimeJets.lean`, Lane Y); (e) neck transport at a
   general time under one comparison (`StrongNeck.exists_transport_tolerance_of_metricComparisonOn`,
   `LocalNeck.exists_transport_tolerance_of_metricComparisonOn`,
   `Perelman/CanonicalNeighborhood/CanonicalWitnessComparisonTransport.lean`, Lane T). NOT
   transported: the cap alternative (`orderedNeckChainTransport`, `LocalCap.map`,
   `StrongNeck.transport'` fix the source time at `0`), the `gradient`/`time_derivative` fields (no
   non-sequential local Shi bound at the target), the ball sandwich and the cap depth margin.
6. **Stage 0 and `t₀ = 0`** (Lanes O and Q delivered): `OrientedThreeStage.exists_uniform_initial_curvature_bound`,
   `IncomingSlab.canonicalOn_of_scalar_le`, `derivativeBoundOn_of_scalar_le`,
   `exists_uniform_initial_canonicalOn_derivativeBoundOn` (`Surgery/Topology/InitialSlabUniformBounds.lean`);
   slab uniqueness from equal initial metrics with scalar, `rmNormSq` and ball transfer across two
   domains (`IncomingSlab.metric_eq_of_initial_eq`, `Surgery/Topology/InitialSlabUniqueness.lean`)
   and the stage-0 `κ` `exists_uniform_kappaNoncollapsed_initial`, still conditional on
   `Perelman.NoLocalCollapsing` per slab because `no_local_collapsing` needs `[ConnectedSpace M]` and
   the stage has no connectedness field (discharge per component via `ComponentBallTransfer`).
8. **Class constraints to add at the next interface revision** (second review): a fixed bound
   `p₀.recenterConstant ≤ Λ` with `Λ` chosen before `C1 C2 τmin Ctime` (C3) and before `κ` (C2), and
   supplied by S together with `ε`; the initial pinching `a₀` derived from the fixed `g₀` and
   propagated by `curvature_preserving`, never a free input.
7. **Exact constants**: build the model witnesses with strict margins (finer accuracy, stronger
   bounds) and take the final `C1 C2` wider, before `κ` and `phi`.

Do not consume the `Has…` predicates of `ExtinctionFrontierLattice` or the `Contract/` global-step
formulation; they are rewrites or refuted (ledger).

## Acceptance

No `sorry`/`axiom`/`nolint`/heartbeat overrides. Build the changed modules and their dependents;
`#print axioms` of each leaf foundational only; the thirteen linters; promotion out of `Skeleton/`
into a producer module next to `CanonicalNeighborhoodInduction.lean`, aggregate registration and
ledger update in the same commit. Intermediate bricks are separate named theorems with their own
acceptance, one new file per brick, never `sorry`s inside a proof.

## Update 2026-09-26 (ACC13)

C2a `historyReducedVolumeMonotone`, C2b `historyReducedVolumeLocalUpperBound` and C2d
`smallScaleNoncollapsingThroughSurgery` are CLOSED in the skeleton (C2d needs
`[SimplyConnectedSpace P₀.Carrier]`, now carried by `noncollapsingThroughSurgery`,
`canonicalNeighborhoodsThroughSurgeryStrong` and the strong assembly's `hcn`). Open C leaves: C2c
`historyReducedVolumeInitialLowerBound` (24a accepted, 24b running in ILBB), C3c `crossingContinuation`
(bricks XA1–XA4, XP1–XP4 accepted; XP2′ and the assembly X7 running), C4 `spatialCanonicalContinuation`
(M5 and C4A's spatial-crossing reduction accepted; I29 not applied). Entry 23 was done by relocation
(34 new files, credit in the commit message). No full-tree builds on this host: the collaborator builds.

ACC14 update (2026-09-26): C2c and C3c CLOSED and wired into the skeleton (`historyReducedVolumeInitialLowerBound_holds`,
lane ILBB, on 20 modules relocated from `origin/codex/wt17-pc-build-warning`, author Bennett Chow;
`crossingContinuation_holds`, lanes XP2′/X7). Open C leaf: C4 `spatialCanonicalContinuation` (lane SX running;
I29 not applied). With S, two skeleton `sorry`s remain.
