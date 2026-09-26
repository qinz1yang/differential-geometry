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
`crossingContinuation` (C3c), `spatialCanonicalContinuation` (C4): seven leaves since ACC7 (C3b
`capWindowContinuation` PROVED, `Surgery/Topology/CapWindowContinuationLeaf.lean`). Since ACC13 four leaves: S, C2c
`historyReducedVolumeInitialLowerBound`, C3c `crossingContinuation`, C4 `spatialCanonicalContinuation`
(C2a/C2b/C2d CLOSED: `historyReducedVolumeMonotone_holds`, `historyReducedVolumeLocalUpperBound_holds`,
`smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace`).

Interface revision (entry 28, 2026-09-26, `Skeleton/DESIGN_28.md`). The ledger's leaves are the
statements now in the tree; the skeleton has exactly the `sorry`s above (eight until ACC7, seven since).
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
| **S** | `UniformDebitSurgeryStep P₀ g₀` for every closed oriented three-manifold: the horn cutoff in Perelman's parameter order (for each horizon `B` an accuracy `ε < 1/11` first; then, given the constants `C1 C2 qcan τmin Ctime` and bounds `δmax ρmax εcap Dcap mcap` of the canonical neighbourhood assumption at that accuracy, cap parameters `p₀` with `modelAccuracy ≤ εcap`, `Dcap ≤ modelRadius`, `mcap ≤ modelOrder`, record bounds `δbound ≤ δmax`, `ρbound ≤ ρmax` and one debit `v`; then, for every class history and singular slab satisfying the derivative bound above `qcan` and the age-restricted canonical neighbourhood assumption, the next event with a record at `p₀`, class closure, boundary-frame-reversing capping, Poincaré-standard discarded components and debit `v` per cut) | **OPEN**; the skeleton leaf is now the strong form `uniformDebitSurgeryStepStrong` (`UniformDebitSurgeryStepStrong`). Content on `origin/codex/pc-sorry-free`: `exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods` (`Contract/PoincareHornCutoffRecord.lean:461`) proves every conclusion of S except the binder order (its cutting accuracy `εcan` follows `∀ accuracy` and `∀ q0`; `Ctime`, `m`, `ηrecord` also precede it) and with the unrestricted (unsatisfiable after a cut) canonical-neighbourhood hypothesis. The chain `c0f94726d a23551e62 e556f139e 95fb763bb 4fe90864a` cherry-picks cleanly onto this lineage (closure needs 6 absent, 31 collaborator-only and 2 both-sides modules). See `Skeleton/HANDOFF_S.md`. Factory bricks B1/B2 (entry 17, accepted 2026-09-26 by ACC4): `fixed` and `recenterConstant` are now chosen before every other input (universal in `Dtrace Dbig r tol Ctime`), and the factory takes the derivative clause `D.slab.DerivativeBoundBefore Ctime qcan D.endTime` as its own hypothesis and reads no `CanonicalWitness.time_derivative`. ACC6: coarse+fine factory F* on spatial witnesses with the `FineCutNecks` premise. ACC7: **S ⇐ `hlong` PROVED** (`Contract/UniformDebitSurgeryStepOfFactory.lean`, `uniformDebitSurgeryStepStrong_of_long_slabs`; G1 = B12, G3, G4 = B14 closed); the one remaining input `hlong` (every singular final slab of a class history below the horizon `B` is long: `2θ ≤ Qc·(s − time last)` for `Qc ≥ Qθ(B, θ)`) is G2 = B13, which is the Crossing X-core applied to horn points (`Skeleton/OPUS_FILL_LOG_SB13.md`) (section ACC7). ACC10: review H12, `hlong` is NOT a supplied input (reduction correct, not refuted); **S ⇐ `FineCutNeckSupply`** (T5, `Contract/UniformDebitSurgeryStepOfFineCutNeckSupply.lean`), T1 DONE, T2 running, T4 blocked on the supply fork (DESIGN_S_SUPPLY running). ACC11: `DESIGN_S_SUPPLY.md` recommends option A (strong-neck class clause; B/C/D dead); review H13 (`consult/H13-s-strong-neck-supply-review-digest.md`): T4′ conditional OK, CN → strong-class supply FIX; interface design (SA1) running, owner decision pending; T2 retired. |
| **C** | `CanonicalNeighborhoodsThroughSurgery P₀ g₀` for every closed oriented three-manifold: Perelman II Proposition 5.1 with the derivative estimate for the class of histories with canonical cutoff records | **Reduced**: the skeleton consumes the strong form `CanonicalNeighborhoodsThroughSurgeryStrong`, reduced (proved, `canonicalNeighborhoodsThroughSurgeryStrong_of_leaves`) to C1–C4; the old form is the induction over the event slabs and, on each slab, the continuation argument up to the supremum of the times before which the assumption holds, live in `Surgery/Topology/CanonicalNeighborhoodInduction.lean` (the old-form assembly was deleted in entry 28); C1 is proved. |
| **C1** | `PinchingThroughSurgery P₀ g₀` | **PROVED** 2026-09-25: `Surgery/Topology/PinchingThroughSurgery.lean`, `pinchingThroughSurgery`, a corollary of `exists_admissiblePinchingFunction_for_identified_incomingSlabs` (`Surgery/Topology/HamiltonIveyPinching.lean`); `phi` independent of `B`, bounds `1`. |
| **C2** | `NoncollapsingThroughSurgery P₀ g₀`: Perelman II 5.2 for the class, history-wide and parabolic: for `B ε C1 C2 τmin Ctime phi` a constant `κ`, then for every threshold `qcan` admissibility bounds, such that for every class history whose past event slabs are canonical (age-restricted) and derivative-bounded, every history parabolic ball (`ObservedHistory.isParabolicallyRmControlledBall`, tracing back through the retained cores) at a time `≤ t₀` of radius `≤ ε` is `κ`-noncollapsed, on an event slab before `t₀ ∈ (start, end]` and on the terminal slab attached by `extendHorizon` before `t₀ ∈ (start, s)` | **Reduced** (proved, `Surgery/Topology/NoncollapsingThroughSurgeryLeaves.lean`, `noncollapsingThroughSurgery_of_reducedVolume_of_smallScale`) to four OPEN skeleton leaves `historyReducedVolumeMonotone`, `historyReducedVolumeLocalUpperBound`, `historyReducedVolumeInitialLowerBound`, `smallScaleNoncollapsingThroughSurgery`. Bricks delivered 2026-09-26: `Surgery/Topology/ReducedVolumeTruncation.lean` (stage scalar floor `exists_stageMetric_scalar_lower_bound` from the cutoff records; `reducedVolume_eq_of_scalar_lower_bound_le`, the reduced volume is independent of the truncation `B ≥ b`; `reducedVolume_lt_top_of_inCutoffClass`; `measurable_regularizedDensity_of_isClosed_regularizedCost_le`). Remaining named hypothesis there: measurability of `regularMinimizerEndpoints` (closed cost sublevel sets; needs compactness of minimizing curves and closedness of `RegularCrossing`), OPEN. KL 78–80: reduced length avoiding the surgery regions, the volume of the surgery caps at scale `h`; tree assets `Perelman/Noncollapsing`, `Perelman/LGeometry`, `Surgery/Topology/HistoryAction*`, `HistoryParabolicBall`, `BackwardPointTrace`; the collaborator's `CapWindowAction` and the action barriers on `origin/codex/wt17-pc-build-warning`. |
| **C3** | `CanonicalNeighborhoodContinuation P₀ g₀`: for `B ε` constants `C1 C2 τmin Ctime`, then for `κ phi` a threshold `qcan` and bounds, such that on an event slab (or the terminal slab) of a class history whose past slabs are canonical and derivative-bounded, if the slab is canonical (age-restricted) and derivative-bounded before `t₀` and the history is `κ`-noncollapsed up to `t₀`, then both hold on `[t₀, t₀ + η)` for some `η > 0` | **Reduced** (proved, `Surgery/Topology/CanonicalNeighborhoodContinuationLeaves.lean`, `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing`) to C3a `DeepContinuation` (**PROVED** 2026-09-26: `Surgery/Topology/DeepContinuation.lean`, `deepContinuation`), C3b `CapWindowContinuation` (**PROVED** 2026-09-26 by ACC7: `Surgery/Topology/CapWindowContinuationLeaf.lean`, `capWindowContinuation` = `capWindowContinuation_of_slab_start_bounds` applied to `RetainedCoreHistory.exists_slice_bounds_at_slab_start` (`Surgery/Topology/SlabStartDerivativeBounds.lean`); half 1 `Surgery/Topology/CapWindowStandardComparison.lean`, `exists_standard_comparison_of_cap_window_trace`) and C3c `CrossingContinuation` (OPEN skeleton leaf; room lemma `Surgery/Topology/CrossingRoom.lean`). Bricks delivered 2026-09-25 (sorry-free; the first five audited): `SlabPointPicking` (2Q picking, curvature bounds on compact slab intervals, `|Rm| ≲ max R 1` from pinching), `SlabBackwardCurvatureControl` (fixed-scale backward control), `UniformKappaCanonicalThreshold` (the tree's uniform `(ε, κ, σ, Phi)` model theorem entered with `κ` as input: witness with the `ε`-only constant from spatial noncollapsing on a backward window inside the slab), `StandardCapCanonicalTransport` (no witness at small normalized age), `Perelman/Noncollapsing/ForwardTransfer` (forward volume transfer), `SlabContinuationDeepInside` (picking with vanishing normalized age; `CanonicalOn` on `[t₀, t₀ + η)` for the points whose window `θ/R` stays inside the slab, from spatial noncollapsing), `Perelman/StandardSolution/CanonicalWitnessPositiveAge` (standard-solution witnesses wherever `τmin ≤ t · R`), `SlabSpatialNoncollapsingBridge` (parabolic to spatial noncollapsing under the derivative bound, for balls whose window lies in the slab and whose curvature scale is `≳ qcan`), `HistoryNoncollapsingToSlab` (history-wide `NoncollapsedBefore` to slab balls), `EventCapCapture` (a point of the new stage without a regular crossing lies in a retained cap; capture at the latest such event), `InitialSlabUniformBounds` and `InitialSlabUniqueness` (stage 0: uniform initial curvature bound, canonical and derivative clauses at low curvature, slab uniqueness from equal initial metrics; the stage-0 `κ` still conditional on per-slab `NoLocalCollapsing`), `Perelman/CanonicalNeighborhood/SpatialClosenessTimeJets` (a `MetricComparisonOn` with time jets from spatial closeness), `Perelman/CanonicalNeighborhood/CanonicalWitnessComparisonTransport` (neck transport at a general time under one comparison), and 2026-09-26: `Perelman/CanonicalNeighborhood/CapComparisonTransport` and `CanonicalAlternativeComparisonTransport` (the time-0 transports `StrongNeck.transport'`, `orderedNeckChainTransport`, `LocalCap.map` generalized to a general time; neck and deep-cap alternatives transported under one `MetricComparisonOn`; positive and round alternatives not transportable locally), `CapWindowDerivativeBounds` (`exists_derivative_gradient_bounds_of_cap_window_trace`: `|∂ₜR| ≤ C'R²` and `|dR| ≤ C'R^{3/2}` at a cap-window point from the standard comparison), `BackwardTraceDistortion` (room lemma `exists_parabolicallyRmControlledBall_or_capWindowPoint` on event slabs; the final-slab case is OPEN, lane X2b). Open: the machinery's noncollapsing hypothesis is spatial at curvature scale `R/θ`, which the bridge cannot supply below `qcan` (parabolic-form refactor under assessment); the crossing case (ages in `[τmin, θ(κ))` with the window through the retained core: blow-up on the common flow, absent local compactness); the scathed case (standard-cap comparison, `wt17` only); the derivative clause at young points; stage-0 connectedness. Second review: `consult/B-poincare-endgame-second-review-digest.md`. See `Skeleton/HANDOFF_C.md`. |
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

### Bricks accepted 2026-09-26 (ACC6; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* C3b: `Surgery/Topology/CapWindowContinuationLeaf` proves the cap-window leaf for slab-interior
  points (`capWindowContinuation_of_slab_interior`) and the full leaf
  `capWindowContinuation_of_slab_start_bounds` from ONE hypothesis `hslice` (proposed name
  `exists_slice_bounds_at_slab_start`: the regularity and the right-derivative bound of `R` at the
  slab start `t₀ = a`). Its inputs: L4e `Perelman/CanonicalNeighborhood/WindowedWitnessEndpointPerturbation`
  and L6e `Perelman/StandardSolution/StandardClosenessEndpointWitness` (endpoint forms, `μ = 0`), L10
  `Surgery/Topology/DerivativeBoundExtension` (derivative/gradient clauses extended past `t₀` from the
  slice), L10b `Surgery/Topology/SlabStartSliceBounds` (the regularity half of `hslice` from
  `smoothUpTo`; `IncomingSlab.exists_slice_bounds_at_slab_start`: both halves on one slab from
  scale-invariant curvature jets at the start, one constant uniform in the slab) and
  `RetainedCrossingJets` (jets of the terminal metric carried through a regular crossing). The bound
  half of `hslice` still needs scale-invariant jet bounds `|∇ᵏRm|² ≤ K R^(k+2)` (k ≤ 2) on the
  post-event slice above the threshold: at retained-core points given the old slab's jet clause near
  its end, on caps/collars OPEN; lane L10c.
* S: the coarse+fine factory F* (lane SFR, `Surgery/Contract/HornFineCutNecks`,
  `HornFineCutoffRecord`, `PoincareHornCutoffRecordOfFineCutNecks`,
  `exists_horn_cutoff_record_with_uniform_volume_debit_of_spatiallyCanonical_of_fineCutNecks`) consumes
  `SpatiallyCanonicalBefore` and a fine-neck premise `TerminalCorePresentation.FineCutNecks εcut Q`
  (`Skeleton/HANDOFF_S.md`). Remaining gaps F* → S: G1 (B12, the fine-neck supply on long slabs)
  running; G2 (B13, short slabs through the history window) OPEN; G3 (ε-monotonicity of spatial
  witnesses) CLOSED by `Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessMonotone`
  (`IncomingSlab.spatiallyCanonicalBefore_mono_eps`); G4 (B14, record bounds and repackaging into S)
  running.
* C3c (Crossing): B3d `Surgery/Topology/BoundedCurvatureAtDistanceBoundedThreshold`
  (`RetainedCoreHistory.exists_scalar_bound_at_distance_of_bounded_threshold`: the single-slab
  headline with the threshold ratio `q ≤ Cq·R(y,t)` in place of `q/Q → 0`; four generalized copies of
  committed helpers, to replace the `q/Q → 0` versions later); B6b'
  `Surgery/Topology/TracedRegionAncientLimitData` (the ancient limit with its survivor maps,
  injectivity, per-time metric identities, `IsSolutionOn`, and the κ volume tests); B7
  `Surgery/Topology/TracedRegionDepthInduction` (B5's `hscal` on the final slab for bounded depth
  `T ≤ 1/(2·Ctime·Q(A))` only; arbitrary depth needs the maximal-window structure, design pending).
  Sixth external review digested: `consult/F-crossing-core-review-digest.md` (B6c-κ by uniform
  reference conversion; B6d and B7 by the maximal-window structure; C3b endpoint route confirmed).
* C2 tools: H3b `Surgery/Topology/HistoryLGeometry/ExponentialSmooth` (openness of the history
  L-exponential domain and smoothness of `historyLExp` near a point, base time interior; event-time
  `T − v²` not covered).

### Accepted 2026-09-26 (ACC7, commit A; sorry-free, foundational axioms, 13 linters clean)

* C3b CLOSED. `capWindowContinuation` (`Surgery/Topology/CapWindowContinuationLeaf.lean`) is
  `capWindowContinuation_of_slab_start_bounds P₀ g₀
  (RetainedCoreHistory.exists_slice_bounds_at_slab_start P₀ g₀)`; axioms [propext,
  Classical.choice, Quot.sound]. The skeleton leaf is deleted (pattern of `deepContinuation`); the
  skeleton now has seven `sorry` leaves. The slice bounds at the slab start (lane L10c,
  `Surgery/Topology/SlabStartDerivativeBounds.lean`) split on the post-event point: in a retained
  cap, standard-cap jets (`StaticCapCurvatureJets`, `exists_presentedStaticCap_window_curvature_bounds`)
  and L10b's jets-to-derivative lemma; otherwise a regular crossing, where the right derivative of
  `R` at the start equals `ΔR + 2|Ric|²` of the terminal metric, the limit of the old slab's
  `∂ₜR` (`CrossingScalarEvolutionRate`), bounded by the old slab's derivative clause (same
  `Ctime`); `k = 0` is vacuous (`R < Q₀ ≤ qcan`). Generic `scalarEvolutionRate g x = Δ_g R_g +
  2|Ric_g|²` with chart formulas, continuity, local-isometry invariance and open restriction:
  `Evolution/Scalar/ScalarLaplacianRicciTerms.lean` (namespace `Geometry.Curvature`).
* C3 assembly: `CrossingContinuation` now binds `δmax ρmax εcap` after `qcan` (lane M6, same order as
  `CapWindowContinuation`); `canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing`
  re-proved; C3, C and the strong assembly foundational.

### Accepted 2026-09-26 (ACC7, commit B; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* S: `uniformDebitSurgeryStepStrong_of_long_slabs P₀ g₀ hlong : UniformDebitSurgeryStepStrong P₀ g₀`
  (`Contract/UniformDebitSurgeryStepOfFactory.lean`, lane SB14), with ONE hypothesis
  `hlong : ∀ B θ > 0, ∃ Qθ, ∀ H ∈ class, H.horizon < B → ∀ s (G : singular final incoming slab from
  H.initialMetric last), s ≤ B → ∀ Qc ≥ Qθ, 2θ ≤ Qc·(s − time last)`. Suppliers: B12
  (`Contract/HornFineCutNecksLongSlab.lean`, `TerminalCorePresentation.exists_fineCutNecks_of_long_terminal_slab`,
  `∃ eta εcone` fixed before `κ ρ C1 C2 Ctime Cgrad phi`; the ball lemma
  `RetainedCoreHistory.exists_terminal_scalar_bound_on_ball_of_final_slab`), the frontier-scalar variant
  of B10/B10b (`Topology/HornSeparationFrontierScalar.lean`), B3e (`Topology/BoundedCurvatureAtDistanceConstants.lean`:
  `coneAccuracy` fixed before the constants), and `IncomingSlab.nonempty_terminalLimitMetric`. ACC7
  folded SB14's three private quantifier-moved copies (≈340 lines) into B3e's and B12's public
  statements. G2 = B13 (`hlong`, short slabs) is OPEN and is the Crossing X-core applied to horn
  points (`Skeleton/OPUS_FILL_LOG_SB13.md`: needs bounded curvature at distance on arbitrary slices,
  maximal traced depth, the ancient κ-limit, and the topological cap-window exclusion).
* C3c (Crossing): B6c-κ PROVED (`Topology/AncientPointedFlowLimitNoncollapsing.lean`,
  `parabolicallyKappaNoncollapsedBelowScale_of_local_pinching_flow_limit`: local approximants give
  `κ/250`-noncollapsing of the ancient limit, completeness from B6c); B6d core PROVED
  (`Topology/AncientPointedFlowLimitBoundedCurvature.lean`, `exists_scalar_bound_of_ancient_pointed_flow_limit`,
  per-slice bounds + derivative clause + Harnack), its two limit-level inputs (spatial witnesses and
  the derivative clause on the limit) are the transfer lane B6D, running; B3e constants as above.
* C2 tools: H3b′ `Topology/HistoryLGeometry/ExponentialFamily` (joint smooth window families of
  history L-geodesics, seams included), H7a `HistoryLGeometry/Jacobian` + `JacobianUnconditional`
  (history L-Jacobian density equal to the single-flow `lJacobianDensity` on windows, its
  τ-derivative and one-sided seam limits, unconditional on the open domain), H6
  `HistoryLGeometry/Index` + `IndexChain` (history index form on window chains, nonnegativity along
  minimizers, no conjugate points before `v`, chain existence; non-seam breakpoints only).
  H7b (Jacobian monotonicity) and H7c (Jacobian limit) running.

### Accepted 2026-09-26 (ACC8; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* C3c (Crossing) / S (B13): B3e on BOTH slabs (lane B3F).
  `RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal`
  (`Topology/BoundedCurvatureAtDistanceSliceTerminal.lean`) and `…_event`
  (`BoundedCurvatureAtDistanceSliceEvent.lean`, via the prefix history `H.prefixAt j.castSucc` of
  `RetainedCoreHistoryPrefix.lean` and the transports of `RetainedCoreHistoryPrefixTransport.lean`),
  plus `eventually_…` sequence forms. Bounded curvature at distance at an arbitrary slice point that
  is not a cap-window point. Suppliers: the chain-of-balls trace capture
  (`BackwardTraceChainCapture.lean`), the scalar bound along the cone-end ray
  (`ConeEndRayScalarBound.lean`), and the traced limit/cone/second-level/positive/buffer forms of
  B3c/B3d (`BoundedCurvatureAtDistance{TracedLimit, TracedCone, TracedSecondLevel, TracedPositive,
  ChainBuffers, Slice}.lean`). OPEN: the rebased form used by `hRP` (¬`CapWindowPoint` at the
  recentre point, review G).
* C3c: B6d's limit-level transfer (`Topology/AncientPointedFlowLimitTransfer.lean`,
  `FiniteHorn.exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants`) is PROVED as
  stated. Its hypothesis `hEreg` (every limit time is eventually non-exceptional) cannot be met by
  the history consumer, so it does not discharge B6d. B11 of `Skeleton/DESIGN_B6D_GLUE.md`
  restates the headline. B6b'' (`TracedRegionAncientLimitWitnesses.lean`) proves the local pull of
  witnesses and the survivor-map derivative bounds. B6d-glue bricks B1
  (`Topology/Sequences/ExceptionalSetApproximation.lean`), B2
  (`Estimates/RicciLowerMetricComparison.lean`), B3
  (`Geometry/Curvature/CurvatureOperator/RicciLowerBound.lean`,
  `Perelman/CanonicalNeighborhood/PinchingRicciLowerBound.lean`) and B12
  (`TracedRegionAncientLimitDerivativeCutoff.lean`) are accepted. B4–B7, B11, NC0, X and
  BASESLICE are running.
* C2 tools: CF (`Topology/HistoryParabolicBallForwardFlow.lean`,
  `ObservedHistory.exists_common_flow_past_time_of_parabolicallyRmControlledBall`) gives the common
  flow past the base time on `closed a t₁` with `t < t₁`, which is route (B) of G1d. H7c
  (`Topology/HistoryLGeometry/JacobianLimit.lean`) gives the small-`v` limit of the history reduced
  Jacobian and the Gaussian bound `exists_pos_historyReducedJacobian_le_gaussian` for history
  minimizers, only for `v` below the window's `δ`. H7b, C2M, C2E, C2W1 and R0 are running.

### Accepted 2026-09-26 (ACC9; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* C2 small-scale (R0, `Skeleton/DESIGN_SMALLSCALE.md` §6.3): a compact simply connected manifold of
  constant positive sectional curvature is isometric to a round sphere
  (`Geometry/Metric/Sphere/Quotient/SimplyConnectedSpaceForm.lean`,
  `exists_isometry_round_sphere_of_constant_positive_sectional_curvature`); the round `n`-sphere has
  volume at least that of the unit `n`-ball (`Geometry/Metric/Sphere/Round/BallVolumeBound.lean`);
  R1 `FiniteHorn.SpatialRoundComponent.volume_lower_of_simplyConnected`
  (`Perelman/CanonicalNeighborhood/SpatialRoundComponentVolume.lean`) with the constant
  `4 * Real.sqrt 3 * Real.pi` (a lower bound, not the exact `6√3π²` of §6.3).
* NC0 (`Perelman/Noncollapsing/TerminalTime.lean`): parabolic κ-noncollapsing below a scale passes to
  the terminal time (`parabolicallyKappaNoncollapsedBelowScale_of_forall_time_lt`); applies to the
  ancient limit's `ancientTimeInterval` with no adapter.
* C2 wave 1 (`Skeleton/DESIGN_C2_ASSEMBLY.md` §5.1–§5.4): G7′ injective area inequality
  (`Analysis/Integration/Measure/Parametric/InjectiveAreaInequality.lean`,
  `lintegral_paramDensity_mul_le_lintegral_image`); TailG uniform Gaussian tail for a bare metric
  (`Perelman/LGeometry/Jacobian/MetricGaussianTail.lean`, `exists_uniform_tail_gaussian_metric`);
  SB1/SB2 at a seam base time (`Topology/HistoryLGeometry/SeamBase.lean`, `…_of_mem_Ico` forms);
  X1–X3 horizon extension (`Topology/HistoryHorizonExtension.lean`, `exists_extendHorizon_gt`,
  `reducedVolume_extendHorizon`; the design's primed `mem_Icc_of_mem_stageDomain'` is
  `mem_Icc_zero_horizon_of_mem_stageDomain`); E2a closed-start velocity limit
  (`Perelman/LGeometry/Geodesic/ClosedStartVelocity.lean`) and E
  (`Topology/HistoryLGeometry/ExponentialClosedStart.lean`,
  `exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain`). C2M (wave 1 M) is running.
* C3c base slice (`Skeleton/DESIGN_BASESLICE.md`, lane BS1): BS1 `SlabTimeWindowContinuity`, BS2
  `SliverWindowData`, BS3/BS4 `CapWindowPointTimeSlack`, BS5 event and terminal forms
  `BoundedCurvatureAtDistanceSliver` (with `SliceBallBoundTransfer`), BS7
  `InitialSlabScalarWindow`. BS6 (post-surgery stage start) is running.
* C3c B6d glue (`Skeleton/DESIGN_B6D_GLUE.md`, lane B6G2): B4 short paths through a local pullback
  (`Geometry/Metric/Pullback/LocalDistance.lean`), B5
  `FiniteHorn.exists_neckAlternatives_localPull_of_metric_lower`
  (`Topology/NeckAlternativesLocalPull.lean`), B6
  `ObservedHistory.exists_neckAlternatives_of_survivor_maps`
  (`Topology/TracedRegionAncientLimitNeckAlternatives.lean`, the producer of B6d's `hW`). B7 is
  delivered (lane B6G3, not yet accepted); its κ-variant is running.

### Accepted 2026-09-26 (ACC10; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* S (`Skeleton/DESIGN_B13.md`, review H12 `consult/H12-s-fineCutNeckSupply-review-digest.md`): `hlong`
  is NOT a supplied input (H12: the reduction `uniformDebitSurgeryStepStrong_of_long_slabs` is correct,
  `hlong` is not refuted, but no supplier exists). T5
  (`Contract/UniformDebitSurgeryStepOfFineCutNeckSupply.lean`): **S ⇐ `FineCutNeckSupply`**
  (`uniformDebitSurgeryStepStrong_of_fineCutNeckSupply`; the supply fixes the cap requirements
  `Rrad ζ₀ δ₀ ρ₀ m₀` before `εc`, `Kfine` after `εc`, then every `p₀`). T1
  (`Topology/TerminalCapSideExclusion.lean`, `TerminalCorePresentation.false_of_terminal_capSide`):
  the terminal cap-side obstruction. T2 is running; T4 (the supply itself) is blocked on the supply
  fork (design lane DESIGN_S_SUPPLY running; H12 gap: T4 must carry the class conjunct
  `p₀.recenterConstant * δbound ≤ 1/2`).
* C3c base slice (lane BS6): BS6, bounded curvature at distance at a post-surgery stage start
  (`Topology/BoundedCurvatureAtDistanceAfterEvent{,Capture,Pullback}.lean`,
  `RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_after_event`). With ACC9,
  BS1–BS7 are all accepted.
* C3c B6d glue: B7 (lane B6G3) uniform-in-`n` time-Lipschitz metric bounds
  (`Metric/Convergence/CovariantDerivative/Norm/ManifoldUniformComparison.lean`,
  `Estimates/{UniformMetricTimeLipschitz, LocalMetricTimeLipschitz}.lean`), the B6b′ limit with time
  control, scalar bound and `e²` metric lower bound, κ input restricted to approximant times before the
  sliver (`Topology/TracedRegionAncientLimitTimeControl.lean`,
  `exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before`),
  single-time κ transfer to a later time (`Perelman/Noncollapsing/EarlierTimeVolume.lean`), κ of the
  limit from approximant times `< 0` (`Topology/AncientPointedFlowLimitTerminalNoncollapsing.lean`);
  B8–B11 (lane B6G4, `Topology/AncientPointedFlowLimitShiftedTransfer.lean`): transfer at shifted
  approximant times and the restated B6d headline
  `exists_scalar_bound_of_ancient_pointed_flow_limit_of_approximants_of_time_lipschitz` (B8 carries three
  extra hypotheses, the metric convergence data, which B11 has). With ACC8/ACC9, glue B1–B12 are all
  accepted; B13 (composed) and the Crossing assembly design are running.
* C2 (lane C9, `DESIGN_C2_ASSEMBLY.md` §5.3):
  `ObservedHistory.exists_lintegral_image_historyMinDomain_core_le`
  (`Topology/HistoryLGeometry/CoreIntegralBound.lean`), the core integral bound with constant `e^{36}`.
  M is running; T9, H7b+, SB3, H8, H9 are pending.
* C2 small-scale (lane SS1, `DESIGN_SMALLSCALE.md`): S3 local Bishop–Gromov ball ratio
  (`Geometry/Comparison/Volume/Bishop/LocalBallRatio.lean`) and its stage form
  (`Topology/StageBallVolumeRatio.lean`); R3/R4 (`Topology/StageComponentSimplyConnected.lean`); S2a/S2
  (`Topology/CapWindowPointScalar.lean`, `Cw = 2`, needs `Dcap + 1 < Dstar`); S1
  (`Topology/BackwardTraceDistortionThreshold.lean`, threshold form of the room lemma, with a final-slab
  twin); R2 (`Perelman/CanonicalNeighborhood/SpatialRoundComponentBallVolume.lean`, stated on the witness,
  no `ε < 1/11`); S4/S4′ (`SpatialCanonicalWitnessBallVolume.lean`). With ACC9's R0/R1: S1–S4, S4′,
  R0–R4 DONE; S0, S6, S7 and the leaf are running.
* C4 (lane C4B1, `DESIGN_C4B.md`): G (`Topology/LocalPullScalarGradient.lean`); M2 in the corrected shape
  (`Perelman/StandardSolution/StandardWindowComparison.lean`: the comparison set has its closure inside
  the window, or is `standardCapWindow D'` with `D' < D`; the design's whole-window form is false); M3
  (`Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessUniverseTransport.lean`, universe-general
  pushforward `…pushforwardOfInjectiveULift`). M1a, M1b, M4, M4★ are running.

### Accepted 2026-09-26 (ACC11; sorry-free, foundational axioms, 13 linters clean)

None of these closes a leaf.
* Crossing, B13 composed headline (lane B6G5, `DESIGN_B6D_GLUE.md` §2):
  `ObservedHistory.exists_bounded_ancient_pointed_flow_limit_of_spatially_canonical_before`
  (`Topology/TracedRegionAncientLimitScalarBound.lean`): the conclusion of the κ-before ancient limit
  (`exists_ancient_pointed_flow_limit_with_time_lipschitz_survivor_maps_of_noncollapsed_before`) plus a
  uniform upper scalar bound of the limit on `s ≤ 0`, from spatial canonical witnesses and derivative
  bounds at approximant times before `t₀ n`. Deltas vs the design: `ht₀ : t₀ n ≤ t n` dropped (unused),
  `hnc` only for `v < t₀ n`. Glue B1–B13 DONE. Assembly design `Skeleton/DESIGN_CROSSING_ASSEMBLY.md`
  (X0–X7, W1) DONE; X4d under review H14; XA1 (X0/X2/X5c/X5d) running.
* C2 M (lane C2M, `DESIGN_C2_ASSEMBLY.md` §5.2): M1 `ObservedHistory.upperSemicontinuous_regularizedCost`
  (`Topology/HistoryLGeometry/CostSemicontinuity.lean`, with the single-flow competitor lemmas
  `Perelman.eventually_exists_lRegularizedAction_lt_of_absolutelyContinuousOnInterval`,
  `Perelman.exists_absolutelyContinuousOnInterval_of_lRegularizedSpeedSq_le`); M3
  `absolutelyContinuousOnInterval_historyLCurve`, `intervalIntegrable_stageRegularizedLagrangian_historyLCurve`,
  `regularizedExtendedAction_historyLCurve_eq_historyLAction_of_mem` (`CurveAction.lean`, whole domain,
  closed start via E2a); M `measurableSet_historyMinDomain` and `measurableSet_historyMinDomain_of_mem_Ioo`
  (`MinDomainMeasurable.lean`). The design's `hT`, `hend` in M1 were unused and dropped. H7b finishing;
  H7b+/T9/SB3/H8/H9 pending.
* C4 (B) (lane C4B2, `DESIGN_C4B.md`, review H11): M1a `SpatialCanonicalWitness.HasMargins`
  (`Perelman/CanonicalNeighborhood/SpatialCanonicalWitnessMargins.lean`) and
  `StandardSolution.exists_spatialCanonicalWitness_with_margins`
  (`Perelman/StandardSolution/StandardSpatialCanonicalMargins.lean`); M1b
  `StandardSolution.exists_{,window_}ball_placement` (`StandardWindowBallPlacement.lean`); M4
  `SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance`
  (`SpatialCanonicalWitnessUniformTransport.lean`; tolerance depends only on `(α, m, C1, C2, Rlow)`, cap
  rebuilt on a single-neck chain as H11 allows); M4★ `exists_window_spatialCanonicalWitness_of_standard_close`
  (`StandardWindowSpatialCanonical.lean`). With ACC10: M1a/M1b/M2/M3/M4/M4★/G DONE; M5 running.
* Root aggregate: the committed `Perelman/CanonicalNeighborhood/CapCoreCylinderAbsorption` is registered.

### Accepted 2026-09-26 (ACC13; sorry-free, foundational axioms, 13 linters clean)

Three leaves close; the skeleton has four `sorry`s (S, C2c, C3c, C4).
* C2d CLOSED (lanes SS2, SS3): `smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace`
  (`Topology/SmallScaleNoncollapsingThroughSurgery.lean`), with `exists_noncollapsedBefore_of_regularTimes`
  (`HistoryNoncollapsingSliceTransfer`) and `exists_initial_layer_noncollapsed` (`InitialLayerNoncollapsing`).
  Route A of `OPUS_FILL_LOG_SS3.md`: `[SimplyConnectedSpace P₀.Carrier]` on the skeleton theorems
  `smallScaleNoncollapsingThroughSurgery`, `noncollapsingThroughSurgery`,
  `canonicalNeighborhoodsThroughSurgeryStrong` and on the `hcn` binders of the strong assembly; definitions
  unchanged. Deferred merge: SS3's private general initial-layer form becomes the public primary theorem.
* C2a/C2b CLOSED (lanes H7b, C2W, C2L): `historyReducedVolumeMonotone_holds`
  (`Topology/HistoryReducedVolumeMonotone.lean`), `historyReducedVolumeLocalUpperBound_holds`
  (`Topology/HistoryReducedVolumeLocalUpperBound.lean`), from the L-family chains and reduced Jacobian
  monotonicity (`HistoryLGeometry/{FamilyChain*, Jacobian*, ActionSplit, AdaptedFieldIcc, AntitoneOffFinite}`),
  closed-start continuity, comparison, the event-base Gaussian bound (`SeamBaseJacobian`), `JacobianGaussian`
  and the tail estimate (`ReducedVolumeTail`).
* C2c brick 24a (lane ILBA): `exists_uniform_regularCrossing_minimizer_of_regularizedCost_lt_of_derivative_before`,
  `exists_uniform_regularMinimizerEndpoint_of_regularizedCost_lt`, on the relocated collaborator modules
  (entry 23, 34 modules, commit with the provenance line). 24b + leaf running (ILBB).
* C3c bricks (Crossing, `DESIGN_CROSSING_ASSEMBLY.md`, `DESIGN_X4D.md`): XA1 (X0/X2/X5c/X5d), XP1 (P1s), XA2
  (X1k, bad point, clause transport), XA3 (ancient limit clauses), XP2 finished part
  (`CapWindowSliceComparison`, `BoundedCurvatureAtDistanceAnchor`), XP3 (W1′ open-closed gluing, local
  pointed flow limits and their noncollapsing), XP4 (`WindowScalarBound`), XA4 (X3p/F3/X3a/X3/X4ext,
  `exists_subseq_depthExtendable_pos`; X3a/X3 carry `ε ≤ crossingNeckAccuracy`). Leaf assembly X7 running.
* C4 bricks: M5 `exists_capWindowPoint_spatialCanonicalWitness` (C4B3); `SpatialCrossingContinuation` and
  `spatialCanonicalContinuationWithAccuracy_of_spatialCrossing` (C4A; interface I29 not applied).
* S bricks (interface A-lite, owner-approved, `Skeleton/DESIGN_STRONG_INTERFACE.md` §4): SP1/SP2/SC1 producers
  (history strong necks, truncated necks, strongly canonical cap windows), SC2–SC6 consumer waves (horn
  neck uniformity, traced regions from strong necks, line/product necks, horizon extension, depth
  induction), SL1 `strongNecksOfCutoffClass_of_strongSpatialCrossing`, SL2 T4′ `FineCutNeckSupplyStrong` and
  T5′ `uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong` (skeleton not rewired).

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
