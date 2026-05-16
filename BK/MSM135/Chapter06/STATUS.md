# MSM135 Chapter 6 Status

Source: `RicciFlow/RicciFlowBooksLatex/MSM135/tex/chapters/chapter6.tex`.

Chapter title: Entropy and No Local Collapsing.

## Scalar/Entropy Statement Layer

| LaTeX labels | BK handle | RicciFlower handle | Status |
|---|---|---|---|
| `notes_and_commentary:lbl543`, `lbl545` | `BK.MSM135.Chapter06.Section01.lbl543_density_normalization` | `RicciFlower.RicciFlow.Perelman.PositiveNormalizedDensity` | Statement interface only. Missing integral normalization over the Riemannian measure. |
| `notes_and_commentary:lbl544` | `BK.MSM135.Chapter06.Section01.lbl544_w_entropy_formula`, `lbl544_w_functional_eq_integral` | `RicciFlower.RicciFlow.Perelman.WEntropyFormula`, `wFunctional` | Concrete measure-theoretic `W` functional is defined as an integral against `u dmu`; the older scalar-input predicate remains for compatibility. |
| `notes_and_commentary:lbl548` | `BK.MSM135.Chapter06.Section01.lbl548_w_entropy_scale_invariance` | `RicciFlower.RicciFlow.Perelman.wFunctional_scale_invariant_of_weightedMeasure_eq` | Proved as an interface bridge from the expected scaling laws for weighted measure, scalar curvature, and gradient-square. Missing metric-layer producers for those laws. |
| unnumbered diffeomorphism invariance after `lbl548` | `BK.MSM135.Chapter06.Section01.w_entropy_diffeomorphism_invariance` | `RicciFlower.RicciFlow.Perelman.wFunctional_diffeomorphism_invariant_of_map` | Proved as a measure-theoretic change-of-variables bridge. Missing metric-layer pullback-volume and scalar/gradient-square compatibility producers. |
| `notes_and_commentary:lbl549` | `BK.MSM135.Chapter06.Section01.lbl549_weighted_measure_variation_factor`, `lbl549_density_variation_producer` | `RicciFlower.RicciFlow.Perelman.wEntropyWeightedMeasureVariationFactor`, `perelmanDensity_hasDerivAt` | Scalar factor is recorded, and the pointwise derivative of `u = (4*pi*tau)^(-n/2) exp(-f)` is proved from `tau' = zeta` and `f' = h`. |
| `notes_and_commentary:lbl550` | `BK.MSM135.Chapter06.Section01.lbl550_weighted_measure_preserving_variation` | `RicciFlower.RicciFlow.Perelman.WEntropyWeightedMeasurePreservingVariation` | Statement interface for weighted-measure-preserving variations. |
| `notes_and_commentary:lbl551`-`lbl552` | `BK.MSM135.Chapter06.Section01.lbl551_entropy_first_variation`, `lbl551_entropy_first_variation_lemma61_of_preIBP`, `lbl551_entropy_first_variation_actual_derivative_of_preIBP`, `lbl551_bracket_variation_producer`, `lbl551_entropy_first_variation_producer_of_volumeVariation` | `RicciFlower.RicciFlow.Perelman.wEntropyBracket_hasDerivAt`, `WEntropyHasFirstVariationAt_of_volumeVariation`, `wEntropyFirstVariation_eq_lemma61_of_hasFirstVariationAt_preIBP` | The scalar bracket derivative and moving-volume base-integral producer are proved. Lemma 6.1 still needs the geometric formula 5.10 producer for the `F` first variation, plus weighted IBP and the base-integral/with-density equality in applications. |
| `notes_and_commentary:lbl553`-`lbl563` | `BK.MSM135.Chapter06.Section01.lbl563_w_entropy_ricci_flow_monotonicity` | `RicciFlower.RicciFlow.Perelman.WEntropyDerivativeFormula`, `WEntropyMonotoneOn` | Statement interface only. Missing conjugate heat equation and square-completion proof. |
| `notes_and_commentary:lbl573`-`lbl587` | `BK.MSM135.Chapter06.Section01.lbl573_epsilon_entropy_formula` | `RicciFlower.RicciFlow.Perelman.EpsilonEntropyFormula` | Statement interface only. Missing unified `F`/`W` variational calculus. |
| `notes_and_commentary:lbl594`-`lbl596` | `BK.MSM135.Chapter06.Section01.lbl594_epsilon_entropy_lower_bound` | `RicciFlower.RicciFlow.Perelman.EpsilonEntropyLowerBound` | Statement interface only. Missing log-Sobolev lower-bound proof. |

## `mu`, `nu`, and Breathers

| LaTeX labels | BK handle | RicciFlower handle | Status |
|---|---|---|---|
| `notes_and_commentary:lbl600`-`lbl603` | `BK.MSM135.Chapter06.Section02.lbl600_mu_functional_lower_bound` | `RicciFlower.RicciFlow.Perelman.MuFunctionalLowerBound` | Statement interface only. Missing admissible-function and infimum API. |
| `notes_and_commentary:lbl608`-`lbl612` | `BK.MSM135.Chapter06.Section02.lbl608_mu_finiteness_and_minimizer` | `RicciFlower.RicciFlow.Perelman.MuFunctionalHasMinimizer` | Statement interface only. Missing compactness/minimizer proof. |
| `notes_and_commentary:lbl613`-`lbl618` | `BK.MSM135.Chapter06.Section02.lbl615_mu_monotonicity`, `lbl618_mu_under_cheeger_gromov_convergence` | `MuMonotoneAlongRicciFlow`, `MuCheegerGromovConvergenceStatement` | Statement interface only. Missing Cheeger-Gromov convergence vocabulary for entropy. |
| `notes_and_commentary:lbl619`-`lbl621` | `BK.MSM135.Chapter06.Section03.lbl620_shrinking_breather_is_gradient_soliton` | `RicciFlower.RicciFlow.Perelman.ShrinkingBreatherIsGradientSoliton` | Statement interface only. Missing breather/soliton structures. |
| `notes_and_commentary:lbl622`-`lbl629` | `BK.MSM135.Chapter06.Section03.lbl626_nu_lower_bound_and_minimizer`, `lbl628_nu_invariant_monotonicity` | `NuFunctionalLowerBound`, `NuFunctionalHasMinimizer`, `NuMonotoneAlongRicciFlow` | Statement interface only. Missing `nu = inf_tau mu(g,tau)` API. |

## Log-Sobolev And Noncollapsing

| LaTeX labels | BK handle | RicciFlower handle | Status |
|---|---|---|---|
| `notes_and_commentary:lbl630`-`lbl645` | `BK.MSM135.Chapter06.Section04.*` | `RicciFlower.RicciFlow.Perelman.LogSobolevInequality` | Statement interface only. Missing Sobolev spaces and Euclidean/manifold log-Sobolev proof. |
| `notes_and_commentary:lbl647`, `lbl652` | `BK.MSM135.Chapter06.Section05.lbl647_kappa_noncollapsed_below_scale` | `RicciFlower.RicciFlow.Perelman.RicciFlowKappaNoncollapsedBelowScale` | Statement interface only. Metric balls are represented by `ScaleControlledBall`. |
| `notes_and_commentary:lbl648`-`lbl651` | `BK.MSM135.Chapter06.Section05.lbl648_*`, `lbl651_*` | `KappaNoncollapsedPreservedUnderLimits`, `KappaNoncollapsedImpliesInjectivityRadiusLowerBound` | Statement interface only. Missing pointed-limit and injectivity-radius comparison APIs. |
| `notes_and_commentary:lbl653`-`lbl657` | `BK.MSM135.Chapter06.Section05.lbl653_*`, `lbl655_*`, `lbl656_*`, `lbl657_*` | `LocallyCollapsingAtTime`, `NoLocalCollapsingTheoremA`, `NoLocalCollapsingTheoremB`, `NoLocalCollapsingLittleLoopEquivalent` | Statement interface only. This is the main hard global analytic frontier. |
| `notes_and_commentary:lbl661`-`lbl676` | `BK.MSM135.Chapter06.Section05.lbl661_*`, `lbl674_*` | `MuControlsVolumeRatios`, `FiniteTimeSingularityModelExists` | Statement interface only. Missing volume-ratio estimates and Hamilton compactness link. |
| `notes_and_commentary:lbl677`-`lbl696` | `BK.MSM135.Chapter06.Section06.*` | improved NLC, Topping, Cheng, heat-equation predicates | Statement interface only. Missing local eigenvalue comparison and diameter-control infrastructure. |

## Further Calculations

| LaTeX labels | BK handle | RicciFlower handle | Status |
|---|---|---|---|
| `notes_and_commentary:lbl697`-`lbl704` | `BK.MSM135.Chapter06.Section07.lbl700_modified_scalar_curvature_variation` | `RicciFlower.RicciFlow.Perelman.ModifiedScalarCurvatureVariation` | Statement interface only. Missing weighted variation proof. |
| `notes_and_commentary:lbl705`-`lbl711` | `BK.MSM135.Chapter06.Section07.lbl705_energy_entropy_second_variation` | `RicciFlower.RicciFlow.Perelman.EnergyEntropySecondVariationFormula` | Statement interface only. Missing second-variation bilinear form. |
| `notes_and_commentary:lbl712`-`lbl715` | `BK.MSM135.Chapter06.Section07.lbl713_matrix_harnack_adjoint_heat_formula` | `RicciFlower.RicciFlow.Perelman.MatrixHarnackAdjointHeatFormula` | Statement interface only. Missing adjoint heat and matrix Harnack package. |

The chapter is now discoverable and label-facing.  Some elementary `W`
variation producers are proved; the next passes should replace broad scalar
inputs with real measure, integral, Sobolev, `F`-variation, and Ricci-flow
solution data.
