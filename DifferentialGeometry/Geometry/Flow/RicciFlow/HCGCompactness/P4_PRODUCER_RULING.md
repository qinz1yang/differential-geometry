# P4 producer architecture ruling

## Scope and baseline

This ruling was re-audited against the aligned short-time-existence branch on
2026-07-22.  It supersedes the earlier ruling that treated
`IteratedRmTowerOn` and the weakly-hypothesized
`BernsteinTower.estimate_complete` as the two canonical solution producers.
The focused-green theorem `open_upgrade_of_raw` remains the consumer endpoint.
This document governs only the remaining producers of that theorem.  It does
not change the public statement of Theorem 3.9 or add a new hypothesis to
`compactnessSol`.

The producer architecture has two independent lanes that meet only near
`ConvFieldOpenAssembly`:

1. the analytic lane: arbitrary-dimensional complete-noncompact Shi estimates,
   then a constants-first source-flow covariant/Lipschitz producer;
2. the provenance lane: a concrete Step-D sidecar retaining canonical-reference
   facts intentionally forgotten by `MetricCompactnessConclusion`.

Do not derive the final data from an arbitrary bare `mc`.  Do not repair or
parameterize the old compact `Fin 3` StarSum chain.  Do not retain the
whole-source bump-collar covariant estimate.

## Analytic lane

### Arbitrary-dimensional curvature tower

The canonical route directly produces `TowerHeatBoundOn` from one costed whole
residual.  The fixed-`card^2`, per-`j` contract in `IteratedRmTowerOn.starBound`
is stronger than, and not derived by, the existing `StarSum2Cost` constructor
tree.  `IteratedRmTowerOn` and `iteratedRmTower_heatBound` remain valid generic
consumer APIs, but `exists_rmTowerSol` must not remain on the trusted solution
route.

The explicit structural costs `rmResidualCost d k` and `rmTowerCost d k`,
their nonnegativity theorems, and `TowerHeatBoundOn.mono_cost` are exact-current.
The level-zero field has also been separated from the
three-dimensional curvature identity: `e0Field_cost_any` proves its exact
arbitrary-index cost, `rmBaseReact` names the eight-term quadratic expression,
and `e0Field_comp_any` proves its component realization.  The solution-facing
join is now exact-current as `e0Residual` (`rmResidual_zero` is the existential
compatibility wrapper): it chooses the global
`e0Field` witness before the point and basis, proves the exact level-zero cost,
and obtains the component heat identity directly from
`rm04Base_of_solution_any`.

The direct residual capstone is exact-current as `rmResidual_cost`.  It
simultaneously provides:

1. one `(4 + k)`-covariant tensor field `T` with
   `StarSum2Cost (Fin d) S t k T (rmResidualCost d k)`; and
2. the exact component time-derivative identity
   `partial_t (nabla^k Rm) = roughLap (nabla^k Rm) + T` in every orthonormal
   basis at the point.

The level-zero Hamilton flow identity is now checked and exact-current as
`rm04Base_of_solution_any`.  It combines `rm04Var_of_sol` with the static
`hamiltonRm04Id`, transports the coordinate formula to an arbitrary fixed
finite orthonormal basis, and proves
`partial_t Rm04 = roughLap Rm04 + hamiltonRmReact` directly from
`IsSolutionOn`.  The earlier consultation in
[`P4_BASE_CONSULT.md`](P4_BASE_CONSULT.md) is therefore resolved.  The fixed
global successor is `resStarNext`; `resStarNext_spec` proves its all-order
component identity, and `rmResidualField` recursively fixes one global
residual before any point or basis.  The complete residual chain is focused-
and exact-green.

The cost must be the explicit recursion followed by the concrete residual
construction, not `Classical.choose` over an existence statement.  Define the
final direct reaction cost by

```lean
noncomputable def rmTowerCost (d k : Nat) : Real :=
  2 * Real.sqrt (Fintype.card (Fin (4 + k) -> Fin d) : Real) *
    (((4 + k : Nat) : Real) * (d : Real) ^ 2 + rmResidualCost d k)
```

The exact-current `towerHeatSol_raw` is assembled pointwise using `nablaKNormHeatAt`,
`StarSum2Cost.bound`, and `nablaKReactionAt_le`.  This requires neither a
global frame nor a per-`j` residual field.  Also provide
`TowerHeatBoundOn.mono_cost`; any recovery of the old literal
`2 * d ^ (6 + k)` coefficient requires a separate proved domination lemma and
must not be assumed.

The first public capstone is:

```lean
theorem towerHeatSol_any
    {alpha t0 omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S)
    (halphat0 : alpha < t0) (ht0omega : t0 < omega)
    (k : Nat) :
    let D' := RealTimeInterval.closedOpen t0 omega ht0omega
    let S' := S.timeRestrict D'
    TowerHeatBoundOn (D := D')
      (nablaKRm04NormSqIntrinsic (I := I) S')
      (nablaKNormLap (I := I) S')
      (rmTowerCost (Module.finrank Real E) k) k
```

It must not require `CompactSpace` or `Module.finrank Real E = 3`.  Its body
must use the direct solution producer above after time restriction.  Once no
call sites remain, delete or explicitly deprecate the sorry-backed
`exists_rmTowerSol` rather than preserving it as an apparent trusted theorem.

### Complete-noncompact Bernstein theorem

The existing abstract signature of `BernsteinTower.estimate_complete` is not a
valid theorem.  Anchor completeness, slabwise metric equivalence, and a Ricci
lower bound do not control the connection or time derivative of cutoffs, and
completeness alone does not give an unrestricted scalar parabolic maximum
principle.  Moreover `BernsteinTower` does not record the first-order Kato
estimate needed to absorb cutoff-gradient terms.

Keep the closed theorem `BernsteinTower.estimate` abstract.  The conditional
noncompact theorem is `BernsteinTower.estimate_of_cutoff` and takes
explicit quantitative parabolic cutoff/exhaustion data together with the Kato
input actually used by the localized induction.  The cutoff package must
record compact support, exhaustion, range, gradient control, parabolic-operator
control, and the regularity required by product rules.  The public no-extra-
input theorem belongs in the solution-specific Ricci-flow layer, where that
package and the curvature-tower Kato estimate are proved from one solution and
its curvature bound.  Do not add either datum as an HCG theorem hypothesis.

### Single-flow and sequence Shi theorems

The HCG-facing owner is a new `HCGCompactness/MovingShiOpen.lean`.

```lean
theorem movingShi_complete
    {D : RealTimeInterval}
    (F : PointedFlowData (I := I) D)
    {alpha beta psi C : Real}
    (halphabeta : alpha < beta)
    (hbetapsi : beta <= psi)
    (hslab : Set.Icc alpha psi <= D.carrier)
    (hreg : Set.Ioc alpha psi <= D.regular)
    (hcomplete : MetricComplete (I := I) (F.atTime (I := I) alpha))
    (hC : 0 <= C)
    (hcurv : forall t in Set.Icc alpha psi, forall x : F.M,
      F.rmNormSq (I := I) t x <= C)
    (N : Nat) :
    exists KShi : Real, 0 <= KShi /\
      MovingShiBoundOn (I := I) Set.univ beta psi
        (fun _ t => F.S.family.metric t) N KShi
```

Only a positive left buffer is required.  There is no future-time buffer.
Completeness is assumed only for the anchor slice `alpha`.

```lean
theorem CurvBoundInput.movingShi_open
    {a b : Real} (h0 : (0 : Real) in Set.Ioo a b)
    (X : PointedFlowSeq (I := I))
    (hD : X.D = RealTimeInterval.openInterval a b 0 h0)
    (hcomplete : CompleteInput (I := I) X)
    (hcurv : CurvBoundInput (I := I) X) :
    forall n N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        MovingShiBoundOn (I := I) Set.univ
          (RealTimeInterval.openWindowLeft a 0 n)
          (RealTimeInterval.openWindowRight b 0 n)
          (fun _ t => (X.term k).S.family.metric t) N KShi
```

The wrapper chooses a strictly larger left window, obtains one curvature
constant uniform in the member index from `CurvBoundInput`, and anchors at the
larger window's left endpoint.  The Shi constant must then be selected by a
constants-first core before the member index.  Merely applying the displayed
single-flow existential separately to each member would choose constants in
the wrong order and does not prove `movingShi_open`.

## Grow-local covariant tail

Change the current `hcovTail` API from all of `Phi.source k` to `bf.grow k`
now.  Keep the public name `covTail_of_bounds`, but replace its statement and
proof with the grow-local form.  Its proof follows `lipTail_of_src`: use
`bf.chi_one` to obtain an open neighborhood on which `gSeqExt = srcMetric`,
then apply restriction invariance of the covariant norm.

Delete from this route:

- `hchi`;
- the support/collar split;
- the uniform bump-family Leibniz estimate;
- target-side reference/equivalence data used only on the collar.

The finite head terms may still use derivatives of each fixed bump and take a
finite maximum after fixing the compact set.

## Constants-first source producer

The owner is a new `HCGCompactness/SourceCovLip.lean`.  It must be source-native:
no `BumpFamily`, `gSeqExt`, target domains, or target-side reference metric.

```lean
structure SrcCovLipData
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (hsrc : SrcSigma Phi) (htgt : TgtSigma Phi)
    (beta psi : Real) : Prop where
  cov :
    forall q : Nat, exists Cq : Real, 0 <= Cq /\
      forall k t, t in Set.Icc beta psi ->
        forall y : SourceDomain (I := I) Phi k,
          metricCovDerivNorm (I := I) q
            (srcMetric (I := I) Phi hsrc htgt k t)
            (refRes (I := I) Phi R hsrc k) y <= Cq
  lip :
    forall p : Nat, exists Lp : Real, 0 <= Lp /\
      forall k s t, s in Set.Icc beta psi -> t in Set.Icc beta psi ->
        forall q, q <= p -> forall y : SourceDomain (I := I) Phi k,
          metricDerivNorm (I := I) q
            (srcMetric (I := I) Phi hsrc htgt k s)
            (srcMetric (I := I) Phi hsrc htgt k t)
            (refRes (I := I) Phi R hsrc k) y <= Lp * |s - t|
```

The producer `srcCovLip_of_soln` consumes one constants-first metric
equivalence, moving-Shi tower, and time-zero covariant envelope.  All output
constants occur before `k`.  It must not invoke compact boundedness separately
for each sequence member.

## Provenance lane

Keep `MetricCompactnessConclusion` unchanged.  Its free `referenceMetric` is a
valid abstraction, so no canonical-reference fact may be asserted for an
arbitrary value of that type.

The concrete owner is `C4/StepDAssembly.lean`:

```lean
structure StepDCanonData
    (X : PointedRiemannianSeq (I := I)) where
  mc : MetricCompactnessConclusion (I := I) X
  ref_eq :
    forall k,
      (mc.convergence.metrics.domain k).referenceMetric =
        (mc.convergence.metrics.domain k).limitMetric
  rel :
    exists Crel : Real, 1 <= Crel /\
      forall k,
        MetricUniformEquivalentOn (I := I) Set.univ
          (mc.convergence.metrics.domain k).limitMetric
          (mc.convergence.metrics.domain k).pullbackMetric Crel
  init_cov :
    forall q, exists Cq : Real, 0 <= Cq /\
      forall k x,
        metricCovDerivNorm (I := I) q
          (mc.convergence.metrics.domain k).pullbackMetric
          (mc.convergence.metrics.domain k).limitMetric x <= Cq
```

The actual source statement includes the stored per-domain instances omitted
above for readability.

Refactor the concrete constructor to:

```lean
noncomputable def compactness_canon
    (P : forall k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    StepDCanonData (I := I) X
```

and retain the existing public entry point by projection:

```lean
noncomputable def compactness_of_b1 ... :
    MetricCompactnessConclusion (I := I) X :=
  (compactness_canon (I := I) P B).mc
```

Add `StepDCanonData.ofSeqSubseq`, then add
`MetricCompactnessInputs.metricCanon` in `C4/MetricCompactnessEndpoint.lean`.
Keep the existing conditional Theorem 3.9 endpoint exactly by projecting `.mc`.

Short adapters `canon_cp`, `canon_rel`, and `canon_init` expose the concrete
facts to P4.  `canon_cp` rewrites the stored convergence by `ref_eq` into the
exact canonical `hcp` shape.  There is no corresponding theorem for arbitrary
`MetricCompactnessConclusion`.

## Ordered implementation

The analytic and provenance lanes run in parallel:

1. add the direct cost API and prove the arbitrary-dimensional
   `rmResidual_cost` theorem;
2. assemble direct `towerHeatSol`, migrate `towerHeatSol_any` and the HCG level
   cost, then remove `exists_rmTowerSol` from the trusted route;
3. use the checked internal parabolic cutoff/exhaustion package and Kato
   producer, and prove the remaining solution-specific cutoff producer;
4. use the checked `BernsteinTower.estimate_of_cutoff`, then prove the
   solution-specific complete Bernstein theorem and revalidate `movingShi_complete` /
   `CurvBoundInput.movingShi_open`;
5. keep the already-complete `StepDCanonData`, `compactness_canon`, and
   `metricCanon` provenance lane unchanged;
6. prove `srcCovLip_of_soln` and consume the existing grow-local
   `covTail_of_bounds` / Lipschitz adapters;
7. keep `canon`, `mc`, `Phi`, `bf`, `srcData`, and `raw` explicit in the
   eventual `compactnessSol` proof before calling `open_upgrade_of_raw`.

## Live implementation status (2026-07-22)

- `open_upgrade_of_raw`: theorem 100%; dedicated consumer machinery 100%.
- grow-local covariant-tail migration: 100%.  The ten-module chain is
  focused-green and exact-refreshed; `hchi` and the whole-source bump-collar
  estimate have been removed from the API and every caller.
- arbitrary-dimensional direct `rmResidual_cost` / `towerHeatSol_raw`: theorem
  completion 100% checked.  The explicit costs, their
  monotonicity/nonnegativity API, and the arbitrary-index level-zero
  cost/component realization are exact-current.  The fixed global successor
  `resStarNext`, its cost/specification theorems, the recursive residual field,
  the one-global-witness capstone `rmResidual_cost`, and the basis-native scalar
  heat assembly `towerHeatSol_raw` are now assembled in source without
  `sorry`; `towerHeatSol_any` is only the positive-tail wrapper and the HCG
  level cost has been migrated to `rmTowerCost`.  The static
  arbitrary-dimensional identity is exact-current as `hamiltonRm04Id`, and
  `rm04Base_of_solution_any` closes the fixed-basis flow-level producer directly
  from `IsSolutionOn`; `e0Residual` is the exact costed base residual.  The base
  theorems are 100%; dedicated direct-tower machinery is 100%.  The ordered
  chain is focused- and exact-green through `MovingShiOpen`; no per-summand
  `IteratedRmTowerOn` assumption or `exists_rmTowerSol` wrapper remains.
- complete-noncompact Bernstein, corrected consumer: 100% checked.
  `GfunCut_parabolic_le` closes the graded finite recurrence and
  `BernsteinTower.estimate_of_cutoff` closes the compact-WMP/exhaustion/error-limit
  capstone; both are exact-current.  The localization machinery plus consumer
  capstone is about 90%.  The remaining independent analytic theorem is the
  solution-generated `ShiCutoffData` producer, still theorem-level 0%; see
  `P4_CUTOFF_CONSULT.md`.  The current weak-signature `estimate_complete` is
  legacy and is not counted as a valid theorem frontier.
- `movingShi_complete` and `CurvBoundInput.movingShi_open`: the wrappers and a
  full source proof of `movingShi_of_bound` are assembled with one explicit
  constant chosen before the sequence member.  The HCG-facing assembly is now
  focused- and exact-green, including the noncompact tower-norm regularity and
  anchor-norm repairs.  These remain wrappers only: their trusted analytic
  foundation is 0% until the remaining solution-produced cutoff theorem is
  closed and the legacy `estimate_complete` call is replaced.
- `StepDCanonData` / `compactness_canon`: 100% checked.  The sidecar,
  subsequence transport, public projection, whole-source canonical bounds, and
  flow-side `canon_cp` / `canon_rel` / `canon_init` adapters are focused- and
  exact-green on the live framed import chain.  The provenance lane is closed.
- `SrcCovLipData`: source-native interface stated and focused-green.
  `srcCovLip_of_soln` remains theorem-level 0% at its single constants-first
  varying-source analytic `sorry`.
- unconditional `compactnessSol`: theorem 0%.
- dedicated P4 consumer machinery remains about 97%; whole-HCG support
  machinery remains about 60%.
