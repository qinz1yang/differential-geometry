# Lead notes, 2026-09-26 (autonomous window 08:30Z–14:30Z)

Decisions taken while the owner is away; the acceptance lane applies the queue/ledger updates.

## Verdicts on bricks

- S-brick B9 (deep-horn ball, purely spatial): FALSE (`OPUS_FILL_LOG_SB9.md`: a cone-like horn end
  is an ε̄-neck at every point with unbounded curvature at finite normalized distance). Folded into
  the Crossing chain's bounded-curvature-at-distance theorem (B3). B11 takes the ball as hypotheses
  (`SeparatingSphereAxialArms.lean`, needs only the separation clause (c), supplied by B10).
- Crossing B3b as first stated: FALSE (`OPUS_FILL_LOG_B3B.md`: a fresh cap inside the backward
  window carries an arbitrary metric, so no trace exists there). Repair (i), being proved: the
  single-slab version with `time (activeStage t) ≤ t − Λ/R`. Repair (ii), later, after B5: the
  Crossing-shaped form with the records and `¬CapWindowPoint`.
- 24a/24b (initial lower bound): blocked on entry 23 (Ziyang's `CapWindowAction` commits);
  `ANALYSIS_ILB.md` has the exact statements; the leaf needs `Λ` (done by I28).
- Closed-start convergence of the L-curve is a hypothesis (`OPUS_FILL_LOG_G1C.md`: flat punctured
  counterexample); the history windows supply it.
- G1d (base time at a closed end without compactness): partial. Decision: route (B): H9 builds the
  common flow on `closed a t'` with `t' > t` whenever the history continues past `t`; leaves that
  need the base time regular are stated for `t < horizon` (the terminal clause uses the extended
  history, where `t` is interior). No L-geometry refactor (`hS → hF`) now.
- G6 needs `[SigmaCompactSpace M]` on the open subset and `T ∈ D.regular`; both handled by (B).
- 27b/27c: the standard solution's young spatial witnesses: initial layer proved; the positive-time
  bounded-curvature band (`BoundedCurvatureSpatiallyCanonical`) is 27c's target via L1 compactness.
- D2: quantifier swap needed (`C'` before the derivative constant), per `DESIGN_C3B.md` brick 0.
- L10b (post-event slice): not needed; the age clause excludes `t₀ = a` for the witness clause and
  the "before" clauses are open at `t₀`.

## Additions 10:45Z

- 27c DONE unconditionally: `StandardSolution.exists_spatialCanonicalWitness_with_cap_neck_charts`
  (`Perelman/StandardSolution/StandardSliceSpatialCanonical.lean`, + `StandardFarRegion.lean`) gives
  spatial witnesses at EVERY point and time `t ∈ [0, Θ]` of every standard solution, one constant;
  `SpatialLocalCap.coreModel` is purely topological (`CapCore`), so no interface change. The old/young
  split in `StandardSpatialCanonical`/`StandardYoungSpatialCanonical` is now redundant (keep as
  corollaries or retire at acceptance).
- B5 delivered with the along-trace curvature bound as a hypothesis (`hscal`); B7 (depth induction
  anchored by the finite-horizon limit bound from B6a) produces it. The bridge's `Cbirth` is
  Θ-independent inside its proof (`WindowPersistence.lean:713`) but not exposed: expose it at
  acceptance (edit `CapWindowStandardComparison.lean`: `Cbirth` before `Θ`).
- DESIGN_C4.md: C4 needs C3's output on `[t₀, t₀+η)` as a hypothesis (15-line interface fix in
  `SpatialCanonicalContinuation.lean` + the strong assembly, lane I28c); case (C) young unscathed
  points share the Crossing "X-core" (forward persistence is NOT a valid route: accuracy loss
  compounds, and young means normalized age `< τmin`, not `c(ε)/R`); the spatial transport API
  (restrict/pushforward/scale/metric-close) is lane SPT.
- H2b delivered (seam C¹ matching; base-at-event case excluded, needs a glued base window).
- G1c helper `isLRegularizedGeodesicOn_lPhaseCurve` made public (used by G1d, G3).

## Acceptance-3 checklist (after ACC2's commit)

1. Interface commit: I28's files (`CanonicalNeighborhoodInduction`, `SpatialCanonicalContinuation`,
   `CanonicalNeighborhoodContinuationLeaves`, `NoncollapsingThroughSurgeryLeaves`,
   `CanonicalNeighborhoodsThroughSurgeryStrong`, `CanonicalCapScalar`, `PinchingThroughSurgery`,
   `ReducedVolumeTruncation`, `Contract/PreparedHistoryCutoff`, `Contract/PoincareHornCutoffRecord`)
   + the skeleton; one lake call including `PoincareEndgame`; 8 sorry leaves; axioms; commit.
2. Bricks: register and build in one call: `Perelman/Noncollapsing/VolumeDistortion`,
   `Perelman/LGeometry/Index/JacobiMinimality`, `Surgery/Topology/HistoryScalarFloor` (retire the
   cutoff-record floor in `ReducedVolumeTruncation` in its favour), `Perelman/LGeometry/Geodesic/
   {ClosedEndExtension, ClosedStartPhase, ClosedStartCurve, ClosedEndBase}`,
   `Solution/ChartCurvatureRegularity`, `Perelman/LGeometry/Jacobian/{Naturality, GramIndexBound}`,
   `Geometry/Connection/ParallelTransport/Naturality/PartialDiffeomorph`,
   `Perelman/LGeometry/Ray/ParabolicBallRange`, `Analysis/Integration/Measure/Parametric/
   AreaInequality`, `Perelman/StandardSolution/{StandardFamilyCompactness,
   StandardInitialSpatialCanonical, StandardYoungSpatialCanonical}`,
   `Perelman/CanonicalNeighborhood/WindowedWitnessStrictRestriction`, `Surgery/Topology/
   {SliverForwardComparison, TracedRegion, TracedRegionBackwardStep, BackwardTraceDistortionTerminal,
   SpatialBoundedCurvatureAtDistance, SeparatingSphereAxialArms, LocalNeckChainAxialArms}` and
   whatever L7/L4/H1/27c/B10/B3b deliver by then.
3. Mechanical merges: make X2's private distortion lemmas public (B4 and X2b need them);
   `ClosedEndExtension.IsLRegularizedCurveOn.of_metric_eq` vs G1b's private copy; G1c's private
   `contDiffAt_chartSeed` vs `lPhaseSeed_smooth`; B4's four copied helpers; X2b's private core vs
   X2's main proof; 27b's `metric_pullback_linearIsometryEquiv_eq` vs `Symmetry`'s.
4. Queue rows: 22 bricks G1–G8 delivered (G1 closed end, G1b/c/d start & end partial as above),
   H0 delivered, H1 running; C3b L1/L2/L3 delivered, L4/L7 running, L8/L9/L10a/L6/leaf assembly
   open; Crossing B1/B2/B4/B3a delivered, B3b(i) running, B5–B8 open; S: B11 delivered, B10 running,
   B9 folded into B3, B13 (history window) open, factory bricks B1–B8/B12/B14 open after I28's
   contract edits; 27b delivered, 27c running.
