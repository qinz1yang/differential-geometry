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
grep -rnE "^theorem [A-Za-z0-9_']+ *: *(smoothPoincareConjecture|topologicalPoincareConjecture|UniformDebitSurgeryStep|CanonicalNeighborhoodsThroughSurgery|PinchingThroughSurgery|NoncollapsingThroughSurgery|CanonicalNeighborhoodContinuation)(\.\{u\})? *:=" DifferentialGeometry
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

| ID | Item | Status |
|---|---|---|
| **S** | `UniformDebitSurgeryStep P₀ g₀` for every closed oriented three-manifold: the horn cutoff in Perelman's parameter order (for each horizon `B` an accuracy `ε < 1/11` first; then, given the constants `C1 C2 qcan τmin Ctime` and bounds `δmax ρmax εcap Dcap mcap` of the canonical neighbourhood assumption at that accuracy, cap parameters `p₀` with `modelAccuracy ≤ εcap`, `Dcap ≤ modelRadius`, `mcap ≤ modelOrder`, record bounds `δbound ≤ δmax`, `ρbound ≤ ρmax` and one debit `v`; then, for every class history and singular slab satisfying the derivative bound above `qcan` and the age-restricted canonical neighbourhood assumption, the next event with a record at `p₀`, class closure, boundary-frame-reversing capping, Poincaré-standard discarded components and debit `v` per cut) | **OPEN** (skeleton leaf `Surgery/Skeleton/PoincareEndgame.lean`). Content on `origin/codex/pc-sorry-free`: `exists_horn_cutoff_record_with_uniform_volume_debit_and_poincareStandardDiscarded_of_canonical_neighborhoods` (`Contract/PoincareHornCutoffRecord.lean:461`) proves every conclusion of S except the binder order (its cutting accuracy `εcan` follows `∀ accuracy` and `∀ q0`; `Ctime`, `m`, `ηrecord` also precede it) and with the unrestricted (unsatisfiable after a cut) canonical-neighbourhood hypothesis. The chain `c0f94726d a23551e62 e556f139e 95fb763bb 4fe90864a` cherry-picks cleanly onto this lineage (closure needs 6 absent, 31 collaborator-only and 2 both-sides modules). See `Skeleton/HANDOFF_S.md`. |
| **C** | `CanonicalNeighborhoodsThroughSurgery P₀ g₀` for every closed oriented three-manifold: Perelman II Proposition 5.1 with the derivative estimate for the class of histories with canonical cutoff records | **Reduced** (proved, `Surgery/Topology/CanonicalNeighborhoodInduction.lean`, `canonicalNeighborhoodsThroughSurgery_of_continuation_of_noncollapsing_of_pinching`) to C2 and C3 by the induction over the event slabs and, on each slab, the continuation argument up to the supremum of the times before which the assumption holds; C1 is proved. |
| **C1** | `PinchingThroughSurgery P₀ g₀` | **PROVED** 2026-09-25: `Surgery/Topology/PinchingThroughSurgery.lean`, `pinchingThroughSurgery`, a corollary of `exists_admissiblePinchingFunction_for_identified_incomingSlabs` (`Surgery/Topology/HamiltonIveyPinching.lean`); `phi` independent of `B`, bounds `1`. |
| **C2** | `NoncollapsingThroughSurgery P₀ g₀`: Perelman II 5.2 for the class, history-wide and parabolic: for `B ε C1 C2 τmin Ctime phi` a constant `κ`, then for every threshold `qcan` admissibility bounds, such that for every class history whose past event slabs are canonical (age-restricted) and derivative-bounded, every history parabolic ball (`ObservedHistory.isParabolicallyRmControlledBall`, tracing back through the retained cores) at a time `≤ t₀` of radius `≤ ε` is `κ`-noncollapsed, on an event slab before `t₀ ∈ (start, end]` and on the terminal slab attached by `extendHorizon` before `t₀ ∈ (start, s)` | **OPEN** (skeleton leaf). KL 78–80: reduced length avoiding the surgery regions, the volume of the surgery caps at scale `h`; tree assets `Perelman/Noncollapsing`, `Perelman/LGeometry`, `Surgery/Topology/HistoryAction*`, `HistoryParabolicBall`, `BackwardPointTrace`; the collaborator's `CapWindowAction` and the action barriers on `origin/codex/wt17-pc-build-warning`. |
| **C3** | `CanonicalNeighborhoodContinuation P₀ g₀`: for `B ε` constants `C1 C2 τmin Ctime`, then for `κ phi` a threshold `qcan` and bounds, such that on an event slab (or the terminal slab) of a class history whose past slabs are canonical and derivative-bounded, if the slab is canonical (age-restricted) and derivative-bounded before `t₀` and the history is `κ`-noncollapsed up to `t₀`, then both hold on `[t₀, t₀ + η)` for some `η > 0` | **OPEN** (skeleton leaf). Bricks delivered 2026-09-25 (sorry-free; the first five audited): `SlabPointPicking` (2Q picking, curvature bounds on compact slab intervals, `|Rm| ≲ max R 1` from pinching), `SlabBackwardCurvatureControl` (fixed-scale backward control), `UniformKappaCanonicalThreshold` (the tree's uniform `(ε, κ, σ, Phi)` model theorem entered with `κ` as input: witness with the `ε`-only constant from spatial noncollapsing on a backward window inside the slab), `StandardCapCanonicalTransport` (no witness at small normalized age), `Perelman/Noncollapsing/ForwardTransfer` (forward volume transfer), `SlabContinuationDeepInside` (picking with vanishing normalized age; `CanonicalOn` on `[t₀, t₀ + η)` for the points whose window `θ/R` stays inside the slab, from spatial noncollapsing), `Perelman/StandardSolution/CanonicalWitnessPositiveAge` (standard-solution witnesses wherever `τmin ≤ t · R`), `SlabSpatialNoncollapsingBridge` (parabolic to spatial noncollapsing under the derivative bound, for balls whose window lies in the slab and whose curvature scale is `≳ qcan`), `HistoryNoncollapsingToSlab` (history-wide `NoncollapsedBefore` to slab balls), `EventCapCapture` (a point of the new stage without a regular crossing lies in a retained cap; capture at the latest such event), `InitialSlabUniformBounds` and `InitialSlabUniqueness` (stage 0: uniform initial curvature bound, canonical and derivative clauses at low curvature, slab uniqueness from equal initial metrics; the stage-0 `κ` still conditional on per-slab `NoLocalCollapsing`), `Perelman/CanonicalNeighborhood/SpatialClosenessTimeJets` (a `MetricComparisonOn` with time jets from spatial closeness), `Perelman/CanonicalNeighborhood/CanonicalWitnessComparisonTransport` (neck transport at a general time under one comparison; cap alternative and derivative fields not transported). Open: the machinery's noncollapsing hypothesis is spatial at curvature scale `R/θ`, which the bridge cannot supply below `qcan` (parabolic-form refactor under assessment); the crossing case (ages in `[τmin, θ(κ))` with the window through the retained core: blow-up on the common flow, absent local compactness); the scathed case (standard-cap comparison, `wt17` only); the derivative clause at young points; stage-0 connectedness. Second review: `consult/B-poincare-endgame-second-review-digest.md`. See `Skeleton/HANDOFF_C.md`. |

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
finite-horizon extension, the width extinction, the compact scalar barrier, and now
`pinchingThroughSurgery`.

## Verification boundary

Branch `codex/pc-target-c`, cut from 22a24821b (Codex `wt17-pc-build-warning` lineage, an ancestor of
`liao/pc-final` @ 82fbe8cb5). Focused builds of the new modules and their closures; no root
`lake build DifferentialGeometry` yet. The collaborator's `origin/codex/pc-sorry-free` holds the
factory that leaf S consumes; it is not merged here. Every new module: module build, `#print axioms`
foundational only for the assembly and the proved leaves, thirteen standard linters clean.
