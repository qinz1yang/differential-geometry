# FREE INPUTS: the single progress ledger for the Poincaré route

**This page is the only yardstick of progress on the Ricci-flow side.** Progress is this list
getting shorter, not the number of conditional assemblies, equivalent rewrites or new files.

**Goal.** `smoothPoincareConjecture` (`Surgery/Poincare.lean`): every closed simply connected smooth
three-manifold is diffeomorphic to the standard three-sphere; `topologicalPoincareConjecture`
follows from it and the smooth-structure input supplied by the Moise route
(`exists_isManifold_three`, branch `codex/moise-endgame`).

## Rules

1. An item is **OPEN** unless the tree contains a theorem whose conclusion is that item and whose
   hypotheses are only instance binders. "Proved conditionally" is OPEN, with its conditions listed
   underneath as further items.
2. A `def … : Prop` naming an obligation is OPEN until such a theorem exists.
3. A theorem `A ↔ B` or `A → B` between two OPEN named inputs is a rewrite. It is recorded in the
   equivalence classes below and never counts as progress.
4. Whoever changes the hypothesis list of an endpoint named here updates this page in the same
   commit.

## How to audit (no compiler needed)

```
grep -rnE "^theorem [A-Za-z0-9_']+ *: *(smoothPoincareConjecture|topologicalPoincareConjecture|UniformDebitSurgeryStepStrong|CanonicalNeighborhoodsThroughSurgeryStrong|PinchingThroughSurgery|NoncollapsingThroughSurgery|CanonicalNeighborhoodContinuation|DeepContinuation|SpatialCanonicalContinuation)(\.\{u\})? *:=" DifferentialGeometry
grep -rn "sorry" DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Skeleton
```

## The tree of inputs

### Level 0
`smoothPoincareConjecture_of_controlledExtinction (hext)` (`Surgery/Poincare.lean:80`), with

```
hext : ∀ (M : ConnectedClosedOrientedManifold 3) [SimplyConnectedSpace M.Carrier]
  (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
  Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)
```

Everything below `hext` is proved: controlled extinction ⇒ Poincaré-standard ⇒ diffeomorphic to
`S³` (`Surgery/Topology/ExtinctionReconstruction`, `poincareStandardSumClosed_holds`).

### Level 1: `hext` (OPEN)
Reduced (proved, `Surgery/Topology/CanonicalNeighborhoodsThroughSurgery.lean`,
`hext_of_uniformDebitSurgeryStep_of_canonicalNeighborhoods`) to the two named inputs below through
the finite-horizon maximal-history argument
(`exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants`,
`Surgery/Topology/SingularEventExtinction.lean`; the volume-debit event bound is
`Surgery/Topology/FiniteHorizonContinuation.lean`). The invariant is
`Inv H := H.hasCanonicalCutoffRecords p₀ δbound ρbound`; the accuracy `ε` is chosen by S and the
constants at that accuracy by C.

Statement repair 2026-09-25 (external review and Lane D,
`consult/A-poincare-endgame-first-review-digest.md`): the canonical-neighbourhood clause is required
only at points of normalized age `τmin ≤ R · (t − a)` (both alternatives of `CanonicalWitness`
contain a `StrongNeck` whose backward window must lie in the slab, so fresh cap points can have
none); C also outputs a cap window radius `Dcap` and a cap model order `mcap` that the class must
respect; the derivative clause `|∂ₜ⁻R| ≤ Ctime R²` stays unrestricted above `qcan`.

Strong interface (2026-09-26). The skeleton now proves `smoothPoincareConjecture_holds` through
`smoothPoincareConjecture_of_uniformDebitSurgeryStepStrong_of_canonicalNeighborhoodsStrong`
(`Surgery/Topology/CanonicalNeighborhoodsThroughSurgeryStrong.lean`): S is
`UniformDebitSurgeryStepStrong` (`∀ B, ∃ Λ, ∀ Ctime, ∃ ε, …`, consuming the gradient, spatial,
pinching `a₀` and κ clauses) and C is `CanonicalNeighborhoodsThroughSurgeryStrong`, assembled by
`canonicalNeighborhoodsThroughSurgeryStrong_of_leaves` from C1, C2, C3 and C4 with no further
hypothesis (the class constraints `p₀.recenterConstant ≤ Λ` and `a₀` are part of the strong
statements). The old `UniformDebitSurgeryStep` / `CanonicalNeighborhoodsThroughSurgery` path stays
in the topology modules and is no longer on the skeleton path. Open leaves = the `sorry`s of
`Skeleton/PoincareEndgame.lean`: `uniformDebitSurgeryStepStrong` (S),
`historyReducedVolumeMonotone`, `historyReducedVolumeLocalUpperBound`,
`historyReducedVolumeInitialLowerBound`, `smallScaleNoncollapsingThroughSurgery` (C2),
`capWindowContinuation` (C3b), `crossingContinuation` (C3c), `spatialCanonicalContinuation` (C4).

Interface revision (entry 28, 2026-09-26, `Skeleton/DESIGN_28.md`). The ledger's leaves are the
statements now in the tree; the skeleton still has exactly the eight `sorry`s above.
* S (`UniformDebitSurgeryStepStrong`) is `∀ B εbar, 0 < B → 0 < εbar → ∃ Λ, 0 < Λ ∧ ∀ Ctime, ∃ ε,
  0 < ε ∧ ε < 1/11 ∧ ε ≤ εbar ∧ …`: it takes an accuracy ceiling `εbar` (supplied by C) and returns
  an accuracy below it.
* C (`CanonicalNeighborhoodsThroughSurgeryStrong`) is `∃ εbar, 0 < εbar ∧ ∀ B ε Λ, 0 < B → 0 < ε →
  ε < 1/11 → ε ≤ εbar → 0 < Λ → CanonicalNeighborhoodsThroughSurgeryStrongAt P₀ g₀ B ε Λ`;
  `hext` runs at accuracy `min (1/22) εbar`. C3 (`CanonicalNeighborhoodContinuation`) and C3c
  (`CrossingContinuation`) start with the same `∃ εbar`.
* The class `InCutoffClass` gained the last conjunct `p₀.recenterConstant * δbound ≤ 1/2`,
  discharged from `p₀.recenterConstant ≤ Λ` by `CutoffParameters.recenterConstant_mul_le_half`.
* The induction carries the spatial clause: `SpatiallyCanonicalBefore/On` and
  `EventSlabsSpatiallyCanonical` now live in `CanonicalNeighborhoodInduction`; C4
  (`SpatialCanonicalContinuation`) outputs `C1s C2s Cs` before `κ` and a floor `q₄` after `κ phi`,
  with a spatial threshold `qcan ≤ qs ≤ Cs * qcan` for every `qcan ≥ q₄`; C3 and C3c take
  `C1s C2s Cs` and a floor `qfloor` and return `qfloor ≤ qcan`.
* Cap parameters are threshold-ordered: the prepared-history and horn-cutoff contract theorems
  (`Contract/PreparedHistoryCutoff`, `Contract/PoincareHornCutoffRecord`) are stated
  `∃ δ ε₀ Λq …, 0 < Λq ∧ ∀ q0, 0 < q0 → …` with `Λq * max q0 1 ≤ Q`, on the variable-threshold
  survival theorem `exists_threshold_uniform_selected_neck_append_backward`.
* New brick `exists_presented_cap_scalar_lower_bound_of_canonical_window_core`
  (`Topology/CanonicalCapScalar.lean`): the core version of the presented-cap scalar lower bound
  (the cap leaf takes `D* := Rcap`).
* The old C assembly `canonicalNeighborhoodsThroughSurgery_of_continuation_of_noncollapsing_of_pinching`
  is deleted (no consumers); the old C is the projection
  `canonicalNeighborhoodsThroughSurgeryOfRecenter_of_strong` (now `∃ εbar, …`).
* Pre-existing boundary slice: `NoncollapsedBefore κ ρ t₀` includes `t = t₀`, the post-surgery
  slice when `t₀ = H.time j.succ`; the small-scale leaf must handle it.

| ID | Item | Status |
|---|---|---|
| **S** | `UniformDebitSurgeryStep P₀ g₀` for every closed oriented three-manifold: the horn cutoff in Perelman's parameter order (for each horizon `B` an accuracy `ε < 1/11` first; then, given the constants `C1 C2 qcan τmin Ctime` and bounds `δmax ρmax εcap Dcap mcap` of the canonical neighbourhood assumption at that accuracy, cap parameters `p₀` with `modelAccuracy ≤ εcap`, `Dcap ≤ modelRadius`, `mcap ≤ modelOrder`, record bounds `δbound ≤ δmax`, `ρbound ≤ ρmax` and one debit `v`; then, for every class history and singular slab satisfying the derivative bound above `qcan` and the age-restricted canonical neighbourhood assumption, the next event with a record at `p₀`, class closure, boundary-frame-reversing capping, Poincaré-standard discarded components and debit `v` per cut) | **OPEN**; the skeleton leaf is now the strong form `uniformDebitSurgeryStepStrong` (`UniformDebitSurgeryStepStrong`). Content on `origin/codex/pc-sorry-free`: `exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods` (`Contract/PoincareHornCutoffRecord.lean:461`) proves every conclusion of S except the binder order (its cutting accuracy `εcan` follows `∀ accuracy` and `∀ q0`; `Ctime`, `m`, `ηrecord` also precede it) and with the unrestricted (unsatisfiable after a cut) canonical-neighbourhood hypothesis. The chain `c0f94726d a23551e62 e556f139e 95fb763bb 4fe90864a` cherry-picks cleanly onto this lineage (closure needs 6 absent, 31 collaborator-only and 2 both-sides modules). See `Skeleton/HANDOFF_S.md`. Factory bricks B1/B2 (entry 17, accepted 2026-09-26 by ACC4): `fixed` and `recenterConstant` are now chosen before every other input (universal in `Dtrace Dbig r tol Ctime`), and the factory takes the derivative clause `D.slab.DerivativeBoundBefore Ctime qcan D.endTime` as its own hypothesis and reads no `CanonicalWitness.time_derivative`. |
| **C** | `CanonicalNeighborhoodsThroughSurgery P₀ g₀` for every closed oriented three-manifold: Perelman II Proposition 5.1 with the derivative estimate for the class of histories with canonical cutoff records | **Reduced**: the skeleton consumes the strong form `CanonicalNeighborhoodsThroughSurgeryStrong`, reduced (proved, `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves`) to C1–C4; the old form is the induction over the event slabs and, on each slab, the continuation argument up to the supremum of the times before which the assumption holds, live in `Surgery/Topology/CanonicalNeighborhoodInduction.lean` (the old-form assembly was deleted in entry 28); C1 is proved. |
| **C1** | `PinchingThroughSurgery P₀ g₀` | **PROVED** 2026-09-25: `Surgery/Topology/PinchingThroughSurgery.lean`, `pinchingThroughSurgery`, a corollary of `exists_admissiblePinchingFunction_for_identified_incomingSlabs` (`Surgery/Topology/HamiltonIveyPinching.lean`); `phi` independent of `B`, bounds `1`. |
| **C2** | `NoncollapsingThroughSurgery P₀ g₀`: Perelman II 5.2 for the class, history-wide and parabolic: for `B ε C1 C2 τmin Ctime phi` a constant `κ`, then for every threshold `qcan` admissibility bounds, such that for every class history whose past event slabs are canonical (age-restricted) and derivative-bounded, every history parabolic ball (`ObservedHistory.isParabolicallyRmControlledBall`, tracing back through the retained cores) at a time `≤ t₀` of radius `≤ ε` is `κ`-noncollapsed, on an event slab before `t₀ ∈ (start, end]` and on the terminal slab attached by `extendHorizon` before `t₀ ∈ (start, s)` | **Reduced** (proved, `Surgery/Topology/NoncollapsingThroughSurgeryLeaves.lean`, `noncollapsingThroughSurgery_of_reducedVolume_of_smallScale`) to four OPEN skeleton leaves `historyReducedVolumeMonotone`, `historyReducedVolumeLocalUpperBound`, `historyReducedVolumeInitialLowerBound`, `smallScaleNoncollapsingThroughSurgery`. Bricks delivered 2026-09-26: `Surgery/Topology/ReducedVolumeTruncation.lean` (stage scalar floor `exists_stageMetric_scalar_lower_bound` from the cutoff records; `reducedVolume_eq_of_scalar_lower_bound_le`, the reduced volume is independent of the truncation `B ≥ b`; `reducedVolume_lt_top_of_inCutoffClass`; `measurable_regularizedDensity_of_isClosed_regularizedCost_le`). Remaining named hypothesis there: measurability of `regularMinimizerEndpoints` (closed cost sublevel sets; needs compactness of minimizing curves and closedness of `RegularCrossing`), OPEN. KL 78–80: reduced length avoiding the surgery regions, the volume of the surgery caps at scale `h`; tree assets `Perelman/Noncollapsing`, `Perelman/LGeometry`, `Surgery/Topology/HistoryAction*`, `HistoryParabolicBall`, `BackwardPointTrace`; the collaborator's `CapWindowAction` and the action barriers on `origin/codex/wt17-pc-build-warning`. |
| **C3** | `CanonicalNeighborhoodContinuation P₀ g₀`: for `B ε` constants `C1 C2 τmin Ctime`, then for `κ phi` a threshold `qcan` and bounds, such that on an event slab (or the terminal slab) of a class history whose past slabs are canonical and derivative-bounded, if the slab is canonical (age-restricted) and derivative-bounded before `t₀` and the history is `κ`-noncollapsed up to `t₀`, then both hold on `[t₀, t₀ + η)` for some `η > 0` | **Reduced** (proved, `Surgery/Topology/CanonicalNeighborhoodContinuationLeaves.lean`, `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing`) to C3a `DeepContinuation` (**PROVED** 2026-09-26: `Surgery/Topology/DeepContinuation.lean`, `deepContinuation`), C3b `CapWindowContinuation` (OPEN skeleton leaf; half 1 `Surgery/Topology/CapWindowStandardComparison.lean`, `exists_standard_comparison_of_cap_window_trace`) and C3c `CrossingContinuation` (OPEN skeleton leaf; room lemma `Surgery/Topology/CrossingRoom.lean`). Bricks delivered 2026-09-25 (sorry-free; the first five audited): `SlabPointPicking` (2Q picking, curvature bounds on compact slab intervals, `|Rm| ≲ max R 1` from pinching), `SlabBackwardCurvatureControl` (fixed-scale backward control), `UniformKappaCanonicalThreshold` (the tree's uniform `(ε, κ, σ, Phi)` model theorem entered with `κ` as input: witness with the `ε`-only constant from spatial noncollapsing on a backward window inside the slab), `StandardCapCanonicalTransport` (no witness at small normalized age), `Perelman/Noncollapsing/ForwardTransfer` (forward volume transfer), `SlabContinuationDeepInside` (picking with vanishing normalized age; `CanonicalOn` on `[t₀, t₀ + η)` for the points whose window `θ/R` stays inside the slab, from spatial noncollapsing), `Perelman/StandardSolution/CanonicalWitnessPositiveAge` (standard-solution witnesses wherever `τmin ≤ t · R`), `SlabSpatialNoncollapsingBridge` (parabolic to spatial noncollapsing under the derivative bound, for balls whose window lies in the slab and whose curvature scale is `≳ qcan`), `HistoryNoncollapsingToSlab` (history-wide `NoncollapsedBefore` to slab balls), `EventCapCapture` (a point of the new stage without a regular crossing lies in a retained cap; capture at the latest such event), `InitialSlabUniformBounds` and `InitialSlabUniqueness` (stage 0: uniform initial curvature bound, canonical and derivative clauses at low curvature, slab uniqueness from equal initial metrics; the stage-0 `κ` still conditional on per-slab `NoLocalCollapsing`), `Perelman/CanonicalNeighborhood/SpatialClosenessTimeJets` (a `MetricComparisonOn` with time jets from spatial closeness), `Perelman/CanonicalNeighborhood/CanonicalWitnessComparisonTransport` (neck transport at a general time under one comparison), and 2026-09-26: `Perelman/CanonicalNeighborhood/CapComparisonTransport` and `CanonicalAlternativeComparisonTransport` (the time-0 transports `StrongNeck.transport'`, `orderedNeckChainTransport`, `LocalCap.map` generalized to a general time; neck and deep-cap alternatives transported under one `MetricComparisonOn`; positive and round alternatives not transportable locally), `CapWindowDerivativeBounds` (`exists_derivative_gradient_bounds_of_cap_window_trace`: `|∂ₜR| ≤ C'R²` and `|dR| ≤ C'R^{3/2}` at a cap-window point from the standard comparison), `BackwardTraceDistortion` (room lemma `exists_parabolicallyRmControlledBall_or_capWindowPoint` on event slabs; the final-slab case is OPEN, lane X2b). Open: the machinery's noncollapsing hypothesis is spatial at curvature scale `R/θ`, which the bridge cannot supply below `qcan` (parabolic-form refactor under assessment); the crossing case (ages in `[τmin, θ(κ))` with the window through the retained core: blow-up on the common flow, absent local compactness); the scathed case (standard-cap comparison, `wt17` only); the derivative clause at young points; stage-0 connectedness. Second review: `consult/B-poincare-endgame-second-review-digest.md`. See `Skeleton/HANDOFF_C.md`. |
| **C4** | `SpatialCanonicalContinuation P₀ g₀` (`Surgery/Topology/SpatialCanonicalContinuation.lean`): the age-free spatial canonical-neighbourhood clause (`SpatialCanonicalWitness`, `Perelman/CanonicalNeighborhood/SpatialCanonicalWitness.lean`) continued along the slabs with the C3 constants | **OPEN** (skeleton leaf `spatialCanonicalContinuation`). Delivered bricks: `HornNeckImprovement` (`exists_strongNeck_threshold_of_minimizing_arms`), `NeckRegionAxialArms`, `NeckChainAxialArms`, `ProspectiveNeckSurvivalVariableThreshold` (`exists_threshold_uniform_selected_neck_append_backward`), `SpatialCanonicalWitnessProjection`, `Geometry/Neck/SpatialSourceBounds`, `LocalNeckChainAxialArms` (`IncomingSlab.exists_strongNeck_threshold_of_localNeckChain`: horn neck threshold from a local neck chain around the point), `Perelman/StandardSolution/StandardSpatialCanonical` (standard-solution spatial witnesses on `[0, Θ]`, `StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts_of_young`, conditional on the named hypothesis `StandardSolution.YoungSpatiallyCanonical` (points with `t·R < τmin`), OPEN, lane 27b). Interface (I28c, ACC5): both branches take C3's output on the slab (`∃ η > 0, DerivativeBoundOn ∧ GradientBoundOn ∧ CanonicalOn` on `[t₀, t₀ + η)`) as a hypothesis; the strong assembly passes the C3 leaf's output (`HANDOFF_C.md`). Spatial transport API (lane SPT, ACC5): `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessTransport` (scale, isometric pushforward along a `PartialDiffeomorph`, restriction to an open set, pushforward along an injective local diffeomorphism) and `SpatialCanonicalWitnessComparisonTransport` (neck and deep-cap alternatives under one `MetricComparisonOn`) delivered; the whole-witness metric-close transport is OPEN (no supplier for the gradient field; `rm` bound only with factor 324; `radius_lower` needs a radius margin; source and target in one universe, so the Type-0 standard window needs a `ULift` step; reference-metric change from `StandardCap.metric` to the source metric; `OPUS_FILL_LOG_SPT.md`). |

### Bricks accepted 2026-09-26 (ACC3; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf; each is a proved theorem family with named hypotheses.
* C2 (reduced volume, entry 22): `Perelman/LGeometry/Geodesic/ClosedEndExtension` (the L-geometry
  of a solution extended past a closed right end; L-objects agree for equal metrics on the closed
  window), `ClosedStartPhase`, `ClosedStartCurve` (closed start of the L-phase flow and of the
  regularized L-curve family; convergence at the start is a hypothesis, `OPUS_FILL_LOG_G1C.md`),
  `ClosedEndBase` (base time at a closed end, metric-only; partial, route (B) of the lead notes),
  `Solution/ChartCurvatureRegularity` (chart Ricci and scalar-derivative regularity from joint
  smoothness), `Perelman/LGeometry/Jacobian/Naturality` (L-geodesics, action and index under local
  isometric pullback) with `Geometry/Connection/ParallelTransport/Naturality/PartialDiffeomorph`,
  `Perelman/LGeometry/Jacobian/GramIndexBound` (trace of the Jacobian Gram derivative bounded by
  the L-index), `Perelman/LGeometry/Index/JacobiMinimality` (index of L-Jacobi fields),
  `Perelman/LGeometry/Ray/ParabolicBallRange`, `Analysis/Integration/Measure/Parametric/AreaInequality`
  (area inequality for parametrized images), `Perelman/Noncollapsing/VolumeDistortion` (volume
  distortion under `|Rm|` bounds), `Surgery/Topology/HistoryScalarFloor` (class-free per-history
  scalar floor, reduced volume finite; the cutoff-record floor in `ReducedVolumeTruncation` is kept
  because `HistoryScalarFloor` imports that module), `Surgery/Topology/HistoryLGeometry/Window`
  (history L-windows: absolutely continuous curves across stages, regularized extended action).
* C3b (cap window): `Perelman/CanonicalNeighborhood/WindowedWitnessStrictRestriction`,
  `WindowedWitnessPerturbation` (windowed witnesses stable under uniform perturbation; recentred
  strict witnesses from flow-time towers), `WindowedModelLocalPull` (windowed and oriented
  witnesses through local pullback).
* C3c (crossing): `Surgery/Topology/SliverForwardComparison` (forward curvature, scalar and metric
  comparison on a thin slice), `TracedRegion` (traced regions, common flows with compact
  neighbourhoods, event and terminal versions), `TracedRegionBackwardStep` (one backward step of
  a trace with the scalar doubling bound), `BackwardTraceDistortionTerminal` (room lemma on the
  final slab, `activeStage t = last`; moving its conclusion from `extendHorizon` to `H` is OPEN),
  `SpatialBoundedCurvatureAtDistance` (scalar bounds along spatial canonical chains at bounded
  distance).
* C4 / S (horn): `SeparatingSphereAxialArms` (minimizing arms and a strong-neck threshold from a
  separating central sphere), `HornCentralSphereSeparation` (the ball-local separation, deep horn
  central-sphere sides; slice transfer accepted by ACC4), `Perelman/StandardSolution/
  StandardInitialSpatialCanonical` and `StandardYoungSpatialCanonical` (initial-layer and young
  spatial witnesses of the standard solution; the positive-time band is discharged by 27c, ACC4), `StandardFamilyCompactness` (subsequential convergence of standard
  solutions on compacta).

### Bricks accepted 2026-09-26 (ACC4; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* 27c (standard solution, closes the standard-solution spatial producer unconditionally):
  `Perelman/StandardSolution/StandardFarRegion` (far radial spatial necks on `[0, Θ]`) and
  `StandardSliceSpatialCanonical` (`StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts`:
  a spatial canonical witness at every point and every time `t ∈ [0, Θ]` of every standard
  solution, one constant; `exists_boundedCurvatureSpatiallyCanonical` discharges the band). The
  old/young split of `StandardSpatialCanonical` / `StandardYoungSpatialCanonical` is now redundant.
* C3b (cap window): L5 `StandardWindowShiftConvergence` (time shift and convergence of standard
  windows), L6 `StandardClosenessWindowedWitness` (`exists_uniform_orientedWitness_of_standard_close`:
  oriented witnesses from standard closeness, with a time margin `μ`), L8/L9
  `Surgery/Topology/CapWindowDerivativeTransfer` (scalar derivative and gradient constants at
  cap-window points). Leaf assembly pending: the C3B lane records two gaps (L6 endpoint form;
  the current-slab derivative clause on `(a, t)`, L10a/L10b), `Skeleton/OPUS_FILL_LOG_C3B.md`.
* C3c (crossing): B5 `TracedRegionOrCapWindow` (traced region or cap-window point, with capture
  age; the along-trace scalar bound is a hypothesis), B6a
  `Geometry/Compactness/CheegerGromov/Pointed/Compactness/CompactBalls` and
  `Compactness/Limits/AncientPointedFlowLimit` (all-radii ancient pointed limit of local
  solutions), B6b `TracedRegionAncientLimit` (traced regions give an ancient pointed limit),
  B6c (1), (2), (5) `AncientPointedFlowLimitCurvature` (`Rm ≥ 0`, slice completeness, κ-solution
  packaging given bounded curvature and parabolic κ), B7 step `TracedRegionDepthStep`, B3b
  repair (i) limit `BoundedCurvatureAtDistanceLimit` (pointed convergence at the scalar escape
  radius on the final slab). OPEN core: B3c (bounded curvature at distance), B6c-κ (κ transfer for
  local approximants), B6d (bounded curvature of the limit), the B7 depth induction.
* C4 / S: B10b `HornSeparationSliceTransfer` (horn central-sphere separation transferred from the
  terminal limit to slices; strong-neck threshold at the slice), A1 on spatial witnesses
  `Surgery/Topology/TerminalSpatialCanonicalAlternatives` and
  `Contract/TerminalCorePresentationOfSpatiallyCanonical` (coarse terminal core presentation from
  spatial canonical witnesses); factory bricks B1/B2 (row S).
* C2 (entry 22): H2a `Surgery/Topology/HistoryLGeometry/Regularity` (regularity of history
  minimizers on stages), H2b `HistoryLGeometry/Seam` (C¹ matching at seams; base at an event
  excluded), G3 `Perelman/LGeometry/Geodesic/WindowSolutionMap` (window solution map of the
  L-phase ODE, chart independence).

Verdicts (lead notes 2026-09-26): S-brick B9 (purely spatial deep-horn ball) is FALSE and is
folded into the crossing theorem B3; B11 takes the ball as hypotheses. Crossing B3b as first stated
is FALSE; repair (i) (single slab, `time (activeStage t) ≤ t − Λ/R`) running, repair (ii) after B5.
G1d: route (B) (common flow on `closed a t'`, `t' > t`; leaves needing a regular base time are
stated for `t < horizon`). 24a/24b (initial lower bound) blocked on entry 23.

### Bricks accepted 2026-09-26 (ACC5; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* C4: interface edit I28c (C4 receives C3's output; `SpatialCanonicalContinuation`,
  `CanonicalNeighborhoodsThroughSurgeryStrong`); spatial transport API (SPT, row C4).
* S (A2 on spatial witnesses, lane SB4): `Surgery/Topology/CompactComponentSpatialClassification`
  and `DiscardedSpatialClassification`
  (`GeometricCutoffRecord.exists_poincareStandardDiscarded_tolerance_of_spatiallyCanonical`: the
  discarded components are Poincaré-standard from `SpatiallyCanonicalBefore` and
  `DerivativeBoundBefore`, conclusion verbatim; the backward-window neck is never read). Open for
  the factory swap: an HEq transport of `SpatiallyCanonicalBefore` for
  `exists_poincareStandardDiscarded_of_retainedEvent_heq_tolerance`.
* C2 tools (entry 22): H3a `Surgery/Topology/HistoryLGeometry/Exponential` (history L-geodesics,
  initial vectors, `historyLExp`, uniqueness), H4 `HistoryLGeometry/MinDomain`
  (`historyMinDomain`, surjectivity `image_historyMinDomain`, density identity
  `regularizedDensity_historyLExp_eq`, reduced volume as an integral over the image), H5
  `HistoryLGeometry/Truncation` (truncation, nesting, `injOn_historyLExp_of_lt`). Base time: the
  surjectivity and injectivity need `T ∈ Ioo (time last) (stageEndTime last)` (base time interior
  to the last stage; `T = time last` needs a seam base window, `T = stageEndTime last` needs G1).
  H3b (openness, total extension) and H6 (index form, `not_conjugate_of_lt`) running.
* C3c (Crossing): B3c PROVED on a single slab: `Surgery/Topology/BoundedCurvatureAtDistanceNecks`,
  `BoundedCurvatureAtDistanceCone`, `BoundedCurvatureAtDistance`
  (`RetainedCoreHistory.exists_scalar_bound_at_distance_of_final_slab_window`: for `ε ≤ εcone`
  (absolute), every `A` has `Q Λ` with `R(z,t) ≤ Q R(y,t)` on `B_t(y, A/√R(y,t))` whenever
  `time last ≤ t − Λ/R(y,t)`, witnesses on the final slice above `q`, derivative, gradient,
  pinching and terminal noncollapsing hold). The Crossing-shaped form (records, `¬CapWindowPoint`,
  repair (ii)) is open. B8 `Surgery/Topology/AncientLimitCanonicalWitness` (canonical witness at
  an old base and derivative/gradient bounds at every base from the ancient limit) delivered,
  CONDITIONAL on B6c-κ and B6d (the κ-solution input), a limit orientation, and B6b's `IsSolutionOn`
  export; its generic transfer
  `exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness` moved to
  `Perelman/CanonicalNeighborhood/WindowedModelCanonicalWitness`. The Cone file duplicates L1's
  private scaled-tests volume lemma publicly
  (`RetainedCoreHistory.normalized_terminal_ball_volume_lower_bound_of_scaled_tests`); left as is.
* C3b: `Surgery/Topology/CapWindowFlowPushforward` (L7a: `partialDiffeomorphOfInjective`, the
  window flow pushed along the survivor map) and `CapWindowContinuationAssembly` (the per-point
  theorem: canonical, derivative and gradient clauses at cap-window points with a time room
  `t + 2ρmax²μ < s` and a derivative clause up to `t + 2ρmax²μ`). The leaf is NOT closed: blocked on
  the L6 endpoint form (`μ = 0`) and the current-slab derivative clause (L10a/L10b).

### Equivalence classes (rewrites; not progress)

* `HasExtinctRetainedCoreHistory M g`, `HasExtinctRetainedCoreTower`, `HasExtinctObservationTower`,
  `HasExtinctObservationNucleusOfCutCapCompletion`, `HasExtinctObservationNucleusWithCompletion`,
  `HasExtinctStandardSideNucleus`, `HasUniformRecordsSurgeryTower`, `HasMorganTianExtinctionInput`,
  `HasSurgeryContinuationTower`, `hasExtinctObservationTower`, `hasCoreCompatibleObservationTower`,
  `hasEmbeddedCoreObservationTower` (`Surgery/Topology/ExtinctionFrontierLattice`,
  `ExtinctionExistenceReduction`, `RetainedCoreExtinctionLevel`, `ExtinctObservationNucleus`): each
  implies `hext`; each is OPEN; the arrows between them are rewrites. The width argument
  (`uniformRecordsAbove_of_scalarLowerBound`, `towerExtinct_of_uniformRecordsAbove`) is proved, so
  `HasSurgeryContinuationTower` is the weakest of these, and it is what S iterated would produce.
* `PoincareExtinctionContracts`, `PinnedPoincareExtinctionContracts`, `GlobalStepInputs`,
  `GlobalStepConclusion` (`Surgery/Contract/Assembly`, `GlobalStepInputsPinnedReduction`, `Terminal`):
  a formulation of one surgery step that does **not** connect to the event chains; the unpinned
  contracts are refuted (`not_nonempty_poincareExtinctionContracts_of_hasNontrivialPositiveHorizonHistory`)
  and `GlobalStepConclusion` is refuted for extinct histories (`GlobalStepObstruction`). Do not
  build on them.

### Proved and consumed
`moise304`-style unconditional producers on this side: `sphericalSpaceFormCovering`,
`disjointBoundaryCollarFamily`, `seifertVanKampenPushout`, `sphereDiffeomorphismIsotopyConnected`,
`isEnlargementInput`, `poincareStandardSumClosed_holds`, the extinction reconstruction, the
finite-horizon extension, the width extinction, the compact scalar barrier,
`pinchingThroughSurgery`, `deepContinuation` (`Surgery/Topology/DeepContinuation.lean`) and the
stage-0 noncollapsing `exists_uniform_kappaNoncollapsed_initial_of_pos`
(`Surgery/Topology/InitialSlabNoncollapsing.lean`).

## Verification boundary

Branch `codex/pc-target-c`, cut from 22a24821b (Codex `wt17-pc-build-warning` lineage, an ancestor of
`liao/pc-final` @ 82fbe8cb5). Focused builds of the new modules and their closures; no root
`lake build DifferentialGeometry` yet. The collaborator's `origin/codex/pc-sorry-free` holds the
factory that leaf S consumes; it is not merged here. Every new module: module build, `#print axioms`
foundational only for the assembly and the proved leaves, thirteen standard linters clean.
