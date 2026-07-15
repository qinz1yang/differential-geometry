# Important Ricci-flow theorem index

Purpose: before trying to prove a major Ricci-flow/Hamilton/HCG statement, search
this file first, then jump to the named Lean theorem.  Many important results are
already proved in producer files and are only consumed later in
`DimensionThree/HamiltonPositiveRicci.lean`.

Do not treat a checked consumer as the producer.  If a theorem below is marked
`frontier`, keep the frontier visible instead of adding a wrapper that just
renames the missing mathematics.

## How to use this file

1. Search by the mathematical phrase: "Ricci evolution", "scalar evolution",
   "Uhlenbeck", "pinching", "3.9", "3.11", "extension criterion".
2. Open the listed Lean file and search for the exact theorem name.
3. Reuse the producer directly when it exists.
4. If the statement is a frontier, add the missing lower producer rather than a
   consumer-side assumption.

## Ricci and scalar evolution

These are the main results Claude has repeatedly failed to find.  They are not
in `HamiltonPositiveRicci.lean`; that file mostly consumes them.

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| Ricci evolution predicate/interface | `RicciEvolutionEquationInFrame` | `Basic/Components.lean` | interface |
| Component Ricci evolution from Christoffel evolution and commutators | `evol_ricci_coordFrameAt_of_christoffelEvolution_nabla2_commutators` | `Evolution/Ricci/CoordinateIdentities.lean` | proved |
| Coordinate Ricci evolution producer | `coordRicciEvol` | `Evolution/Ricci/CoordinateIdentities.lean` | proved |
| Local/frame Ricci evolution from variation commutators | `ricciEvolution_of_variation_commutators` | `Evolution/Ricci/Commutator.lean` | proved |
| Local Ricci evolution variants | `ricciEvolutionEquationInFrameOnLocal_of_variation_commutators`, `ricciEvolLocal` | `Evolution/Ricci/Commutator.lean` | proved |
| Lichnerowicz Ricci evolution from Ricci evolution | `ricciLichnerowiczEquationInFrame_of_ricciEvolution` | `Evolution/Ricci/Lichnerowicz.lean` | proved |
| Symmetric/L-C Lichnerowicz variants | `ricciLichnerowiczEquationInFrame_of_ricciEvolution_and_symm`, `ricciLichnerowiczEquationInFrame_of_ricciEvolution_lc` | `Evolution/Ricci/Lichnerowicz.lean` | proved |
| Coordinate Lichnerowicz Ricci evolution | `evol_ricci_lichnerowicz_coordFrameAt_of_christoffelEvolution_nabla2_commutators` | `Evolution/Ricci/Lichnerowicz.lean` | proved |
| Scalar evolution from contracted Bianchi | `scalarEvolutionEquationOn_of_contractedBianchi` | `Evolution/Scalar/Basic.lean` | proved |
| Scalar evolution from Ricci evolution | `scalarEvolutionEquationOn_of_ricciEvolution` | `Evolution/Scalar/Assembly.lean` | proved |
| Regular/L-C scalar evolution variants | `scalarEvolutionEquationOn_of_ricciEvolution_regular`, `scalarEvolutionEquationOn_of_ricciEvolution_lc` | `Evolution/Scalar/Assembly.lean` | proved |
| Smooth solution scalar evolution wrapper | `scalarEvolOfSmooth` | `Evolution/Scalar/Basic.lean` | proved |

Rule of thumb: if a task asks for `d_t R = Delta R + 2 |Ric|^2`, start at
`scalarEvolutionEquationOn_of_ricciEvolution` or `scalarEvolOfSmooth`.  Do not
rebuild Ricci evolution inside Hamilton.

## Metric, inverse metric, and connection evolution

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| Inverse-metric evolution from differentiated inverse identity | `inverseMetricEvolutionEquationInFrame_of_inverse_components` | `Evolution/Metric/Evolution.lean` | proved |
| Coordinate inverse-metric evolution | `coordInvEvol` | `Evolution/Metric/Evolution.lean` | proved |
| Inverse-metric evolution in a frame | `evol_inverse_metric_inFrame` | `Evolution/Metric/Evolution.lean` | proved |
| Metric covariant derivative from Ricci-flow metric variation | `metricCovDerivDerivativeComponents_of_ricciFlow` | `Evolution/Connection/Components.lean` | proved |
| Variable connection-difference derivative | `variableMetricConnectionDiffDerivative_of_metricCovDeriv` | `Evolution/Connection/Components.lean` | proved |
| Christoffel evolution from metric variation | `christoffelMetricVariationEquationInFrameOn_of_metricVariation` | `Evolution/Connection/Producers.lean` | proved |
| Christoffel evolution from Ricci-flow metric variation | `christoffelEvolution_of_ricciFlowMetricVariation` | `Evolution/Connection/Producers.lean` | proved |
| Spacetime-smooth Christoffel evolution | `christoffelEvolution_of_spacetimeSmoothMetric` | `Evolution/Connection/Producers.lean` | proved |

## Riemann/Uhlenbeck/nabla Rm evolution and BBS

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| Uhlenbeck curvature evolution predicate | `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` | `Evolution/Uhlenbeck.lean` | interface |
| Pointwise dim-3 Uhlenbeck-base Rm evolution | `rm04BaseEvolution_at` | `Evolution/UhlenbeckBaseProducer.lean` | proved in current worktree |
| Coordinate-frame Rm time-derivative producer | `rm04HrmProducer` | `Evolution/UhlenbeckBaseProducer.lean` | proved in current worktree |
| Time derivative of level-1 iterated Rm components | `iteratedRmComp_one_hasDerivWithinAt` | `Evolution/NablaRiemannTimeDeriv.lean` | proved |
| Assembled time derivative of nabla^k Rm | `nablaKRm_timeDeriv_of_solution` | `Evolution/Connection/NablaKRmTimeDeriv.lean` | proved |
| Rm norm heat equation from solution | `rm04NormHeatEquationOn_of_solution` | `Evolution/RiemannNormHeatProducer.lean` | proved |
| nabla Rm norm heat bound, scalar form | `nablaRm04NormHeatBoundOn_scalar` | `Evolution/NablaRiemannHeatSolution.lean` | proved |
| Intrinsic nabla Rm norm heat equation | `nablaRm04NormHeatEquationOn_intrinsic` | `Evolution/NablaRiemannHeatFull.lean` | proved |
| First Bernstein-Shi derivative estimate | `bernstein_first_derivative_estimate` | `Evolution/BernsteinShi.lean` | proved |
| Solution-level Bernstein-Shi estimate | `bernsteinShi_solution_estimate` | `Evolution/BernsteinShiSolution.lean` | proved |

Check the theorem hypotheses before using these.  Some older Uhlenbeck wrappers
take `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` as an input, while
`UhlenbeckBaseProducer.lean` is the newer producer side.

## Hamilton dimension-three algebra and pinching

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| Symmetric Ricci eigenbasis | `ricciEigen3`, `ricciEigenBasis3` | `Geometry/Curvature/DimensionThree/RicciControlsRm.lean` | proved |
| 3D standard Rm from Ricci components | `standardRmCompAt_apply` | `Geometry/Curvature/DimensionThree/RiemannFromRicci.lean` | proved |
| Norm of 3D standard Rm | `stdRmNormSq3_at`, `normSq0S_four_eq_stdRmNormSq3` | `Geometry/Curvature/DimensionThree/RicciControlsRm.lean` | proved |
| Rm bounded by scalar/Ricci in dim 3 | `stdRmNormSq3_at_le` | `Geometry/Curvature/DimensionThree/RicciControlsRm.lean` | proved |
| Initial Ricci positivity gives pinching data | `boundsPos_ricMin`, `pinchInitLt_bounds` | `Evolution/RicciPreservation.lean` | proved |
| Shifted pinching preservation | `pinch_sol_closed`, `pinch_sol_closed_nonneg` | `Evolution/RicciPreservation.lean` | proved |
| Trace-free Ricci heat/pinching core | `tfHeat_*`, especially `tfHeat_sol`, `tfHeat_ricci` | `Evolution/ImprovedPinching/*` | proved wrappers |
| Hamilton improved pinching estimate | `pinchEstimate_sol`, `pinchEstimate_ext` | `Evolution/ImprovedPinching/Estimate.lean` | proved |
| Local pinching evolution inequality | `tracefree_rm_pinching_evolution` | `Evolution/LocalPinching.lean` | proved |

## HamiltonPositiveRicci main chain

The main file is `DimensionThree/HamiltonPositiveRicci.lean`.  It is a consumer
and assembly file.  Do not reprove lower evolution identities here.

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| Short-time existence wrapper | `ham3_short_exists` | `DimensionThree/HamiltonPositiveRicci.lean` | checked |
| Short-time solution candidate data | `ham3_short_solution_candidate` | same | checked |
| Short-time `IsSolutionOn` bridge | `ham3_short_isSolution` | same | frontier/sorry |
| Short-time smooth solution | `ham3_short_smooth_solution` | same | checked modulo previous frontier |
| Maximal normalized flow existence | `ham3_flow_exists_normalized` | same | frontier/sorry |
| Unbounded scalar curvature from finite-time blowup | `ham3_scalar_blowup` | same | checked |
| Blowup point selection | `ham3_point_select` | same | checked |
| Section 9 pinching preservation | `ham3_pinch9_fixed`, `ham3_pinch9` | same | checked |
| Section 9 Ricci nonnegativity | `ham3_ric_nonneg9`, `ham3_rescaled_ric_nonneg` | same | checked |
| Positive scalar on rescaled flows | `ham3_scalar_pos` | same | checked |
| Section 10 improved pinching estimate | `ham3_pinch_imp_can`, `ham3_pinch_imp` | same | checked |
| Rm bound on the rescaled window | `ham3_rm_bound` | same | checked |
| Genuine rescaled ball/curvature-control realization | `ham3RescaledBall`, `ham3_rm_control` | same | checked |
| Honest Hamilton compactness input package | `Ham3RmBound`, `Ham3CompactInput` | same | checked contract; producer endpoint still open |
| CGH source realizes selected rescalings | `Ham3SourceRealizes`, `Ham3SourceLink.realizes` | main file + `HCGCompactness/HamiltonPositiveRicciAdapter.lean` | checked contract/adapter |
| Actual-witness Hamilton CGH adapter | `HamCGHConclusion`, `toHam3Exists` | `HCGCompactness/HamiltonPositiveRicciAdapter.lean` | checked conditional consumer |
| Canonical flow-metric ball and volume predicates | `FlowMetricBall`, `FlowMetricBall.IsRmControlled`, `FlowMetricBall.IsKappaNoncollapsed` | `Perelman/Noncollapsing.lean` | checked definitions/support |
| Perelman noncollapse input | `ham3_noncollapse` | `DimensionThree/HamiltonPositiveRicci.lean` | frontier/sorry |
| CGH limit input | `ham3_cgh_limit` | same | frontier/sorry |
| Limit Ricci nonnegativity | `limit_ric_nonneg` | same | checked |
| Base scalar normalization in limit | `limit_base_scalar_one` | same | checked |
| Limit scalar nonnegativity | `limit_scalar_nonneg` | same | checked |
| Pinching decay in the limit | `limit_tf_decay` | same | checked |
| Trace-free Ricci vanishing in the limit | `limit_tf_zero_of_decay`, `limit_tf_zero` | same | checked |
| Einstein limit implies constant sectional curvature | `limit_const_sec_of_einstein` | same | checked |
| Constant positive curvature in the limit | `limit_const_pos` | same | checked |
| Transfer from compact limit back to original manifold | `limit_to_orig` | same | checked |
| Reverse space-form metric construction | `spaceForm_const_metric` | same | checked |
| Constant metric conclusion | `ham3_const_metric` | same | checked modulo frontiers |
| Final Hamilton theorem | `ham3_main`, `thm_2_1` | same | checked modulo frontiers |

## Short-time and maximal continuation

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| Restart short-time from a smooth endpoint metric | `restart_short_time` | `Evolution/CinftyLimitGlue.lean` | interface/producer |
| Construct an extended Ricci flow by smooth glue | `ricci_flow_extends_construction` | `Evolution/CinftyLimitGlue.lean` | checked construction |
| Bounded curvature implies extension past endpoint | `extends_of_rmBounded` | `MaximalTime.lean` | frontier/sorry |
| Maximal finite endpoint implies Rm unbounded | `rmUnbounded_of_maximal` | `MaximalTime.lean` | checked consumer of `extends_of_rmBounded` |
| Maximal finite endpoint forms singularity | `formsSing_of_maximal`, `formsSing_of_maximal_metric` | `MaximalTime.lean` | checked consumer |

If working on Hamilton long-time existence, the real missing theorem is
`extends_of_rmBounded`, not the already-checked consumers below it.

## HCG compactness and MSM135 Chapter 3/4

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| MSM135 3.11 order-p metric derivative assembly | `metricCovOrderWindow_of_evolution` | `HCGCompactness/AllTimesBounds.lean` | proved honest-input theorem |
| MSM135 3.11 mixed q-layer assembly | `metricMixedQWindow_of_evolution` | `HCGCompactness/AllTimesBounds.lean` | proved honest-input theorem |
| Full all-times conclusion package | `metricAllTimes` | `HCGCompactness/AllTimesBounds.lean` | checked assembly |
| Abstract product norm bound P(m) | `compL2_iterCovComp_contrTail_le` | `HCGCompactness/AkMFold.lean` | proved |
| ISO residual bound | `compL2_isoResidual_le` | `HCGCompactness/AkMFold.lean` | proved |
| Abstract Claim 1 | `claim1_abstract` | `HCGCompactness/AkMFold.lean` | proved abstract theorem |
| Conditional MSM135 3.9 metric compactness endpoint | `MetricCompactnessInputs.metricCompactness` | `HCGCompactness/C4/MetricCompactnessInputs.lean` | frontier/sorry |
| Unconditional MSM135 3.9 metric compactness endpoint | `metricCompactness` | `HCGCompactness/MetricCompactness.lean` | frontier/sorry |
| Concrete 3.9-to-3.10 consumer | `solutionComp_of_mc` | `HCGCompactness/SolutionCompactness.lean` | checked consumer of explicit `FlowUpgradeData` |
| Canonical conditional MSM135 3.10 wrapper | `solutionComp_cond` | `HCGCompactness/C4/SolutionCompactnessInputs.lean` | checked conditional consumer; upstream 3.9 frontier remains 0% |
| Canonical public Hamilton compactness wrapper | `compactnessSol_cond` | `HCGCompactness/HamiltonCompactness.lean` | checked conditional consumer |
| Adapter into Hamilton 3D CGH output | `cghToHam3`, `toHam3Exists` | `HCGCompactness/HamiltonPositiveRicciAdapter.lean` | checked map-retaining adapter |
| Bonnet--Myers compactness of a pointed limit | `PointedRiemannianManifold.compact_of_ricci` | `HCGCompactness/PointedConvergenceGlobal.lean` | checked support |
| Compact-limit maps become global | `PointedCGHMaps.exists_source_univ`, `target_univ`, `globalDiffeomorph` | same | checked support |

Important distinction:

- `metricAllTimes` / `claim1_abstract` are not a proof of MSM135 3.9.
- `metricCompactness` is still the honest 3.9 global compactness frontier.
- The live 3.10 consumer API is `solutionComp_of_mc`, `solutionComp_cond`, and
  `compactnessSol_cond`; the former exact-conclusion compatibility API was removed.
- Whole-HCG machinery is conservatively about **45%**; the HCG endpoint
  theorems remain **0%**.  The checked `limit_to_orig` consumer does not prove
  its `ham3_cgh_limit` producer.
- The geometric Claim 1 still needs the `hrelB`/Koszul discharge, inverse metric
  wiring, and upper-tower realization bridge before it becomes the full geometric
  producer used in 3.11.

## Direct limits, Step B, and approximate-isometry support

These are Chapter 4 support files that may be relevant to 3.9 but do not close
`metricCompactness` by themselves.

| Role | Theorem / definition | File | Status |
| --- | --- | --- | --- |
| Sequential direct-limit data | `SeqSystem`, `Lim`, `incl` | `Geometry/Topology/DirectLimit.lean` | checked support |
| Direct-limit injectivity/open-cover/compactness support | `incl_injective`, `incl_isOpenMap`, `isCompact_exists`, `sigmaCompact`, `t2Space` | same | checked support |
| Normal transition map inputs | `normalTransition`, `NormalTransitionDerivBound`, `ExpInverseDerivBoundInput` | `HCGCompactness/C4/StepBInputs.lean` | checked support |
| Approximate-isometry composition constants | `compApproxConst`, `metricEquiv_comp_eps`, `compEpsAccum` | `HCGCompactness/C4/ApproxIsometryComp.lean` | checked support |
| Honest B1 conditional assembly | `StepB1RawInput`, `stepB1_of_raw` | `HCGCompactness/C4/StepB1ApproxIso.lean` | checked assembly; raw producer and textbook endpoint 0% |
| Center-map derivative bounds through order two | `cmChartDerivLe2` | `HCGCompactness/C4/StepCDerivBounds.lean` | checked for `j ≤ 2`; arbitrary-order endpoint unstated/0% |
| Radial Jacobi variation core | `exists_radial_jacobi_radius` | `Geometry/Exponential/JacobiVariation.lean` | checked support |

Warning: the old `ApproximateIsometry.lean` monolith was deleted.  Its durable
interface is `HCGCompactness/C4/ApproxIsometryDefs.lean`; its failed historical
route is retained only in `HCGCompactness/ApproximateIsometryArchive.md`.  Do
not plan work against, or try to repair, the deleted path.

## Known honest frontiers

Fill plans (live-updated 2026-07-09): the original eight `ham3_main` frontiers
are audited in `DimensionThree/HAM3_BLACKBOX_PLAN.md`; six remain open.  The program-level roadmap and
infrastructure gap list is `POINCARE_PLAN.md`.

Do not hide these behind new wrappers:

| Frontier | File | What remains |
| --- | --- | --- |
| `ham3_short_isSolution` | `DimensionThree/HamiltonPositiveRicci.lean` | short-time raw data to `IsSolutionOn` bridge |
| `ham3_flow_exists_normalized` | same | maximal continuation / extension criterion |
| `extends_of_rmBounded` | `MaximalTime.lean` | global bounded-curvature extension theorem |
| `ham3_noncollapse` | `DimensionThree/HamiltonPositiveRicci.lean` | Perelman noncollapse producer/adapter |
| `ham3_cgh_limit` | same | Hamilton-CGH compactness producer |
| `metricCompactness` | `HCGCompactness/MetricCompactness.lean` | MSM135 3.9 Cheeger-Gromov compactness proof |
| `ham3_space_box` | `DimensionThree/HamiltonPositiveRicci.lean` | global spherical space-form classification |
| geometric Claim 1 for HCG 3.11 | `HCGCompactness/AkMFold.lean`, `HCGCompactness/RicBoundProof.md` | `hrelB`, inverse metric wiring, upper-tower realization |

## Search snippets

Useful commands:

```powershell
rg -n "coordRicciEvol|scalarEvolutionEquationOn_of_ricciEvolution|scalarEvolOfSmooth" DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution
rg -n "rm04BaseEvolution_at|rm04HrmProducer|nablaKRm_timeDeriv_of_solution" DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution
rg -n "metricCompactness|solutionComp_of_mc|solutionComp_cond|compactnessSol_cond|toHam3Exists" DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness
rg -n "extends_of_rmBounded|ham3_flow_exists_normalized" DifferentialGeometry/Geometry/Flow/RicciFlow
rg -n "claim1_abstract|compL2_isoResidual_le|metricCovOrderWindow_of_evolution" DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness
```
