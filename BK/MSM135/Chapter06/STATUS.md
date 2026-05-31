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
| Chapter 5 formula `notes_and_commentary:lbl453`, used by Chapter 6.1 Lemma 6.1 | `BK.MSM135.Chapter06.Section01.lbl453_f_functional`, `lbl453_exp_density_variation_producer`, `lbl453_exp_weighted_measure_variation_producer`, `lbl453_f_first_variation_producer_of_volumeVariation`, `lbl453_weighted_green`, `lbl453_weighted_divergence_zero`, `lbl453_shifted_trace_green`, `lbl453_f_formula510_statement`, `lbl453_f_formula510_assembly`, `lbl453_f_formula510_trace_field`, `lbl453_f_formula510_trace_intrinsic`, `lbl453_f_formula510_trace_action`, `lbl453_f_formula510_weighted_trace`, `lbl453_f_formula510_weighted_trace_raw`, `lbl453_f_formula510_trace_chart`, `lbl453_f_formula510_trace_voss`, `lbl453_f_formula510_trace_product`, `lbl453_f_formula510_trace_chart_onE`, `lbl453_f_formula510_trace_chart_partial`, `lbl453_f_formula510_trace_chart_center`, `lbl453_f_formula510_trace_explicit`, `lbl453_f_formula510_final`, `lbl453_f_formula510_canonical_variation` | `RicciFlower.RicciFlow.Perelman.fFunctional`, `FHasVariation`, `f_firstVariation_formula510`, `expNegPotentialDensity_hasDerivAt`, `expWeightedMeasureIntegral_hasDerivAt_at`, `FFunctionalHasFirstVariationAt_of_volumeVariation`, `FFunctionalFormula510`, `formula510_of_steps`, `formula510_of_ints`, `formula510_of_connTrace`, `formula510_of_connTraceField`, `formula510_of_trace`, `connTraceAction_coord`, `connTraceAction_eq_gamma`, `weightedTrace_eq`, `weightedTrace_of_raw`, `gammaRawDivergenceTrace`, `christoffelWeightedDivergenceTrace`, `connTraceChartCoeff_eventually`, `connTraceChartCoeffOnE_eventually`, `connTraceChartCoeff_partial`, `connTraceChartCoeff_center`, `connTraceRawDiv_voss`, `connTraceRawDiv_chart_product`, `connTraceRawDiv_chart_explicit`, `RicciFlower.Analysis.DivergenceTheorem.divergence_g_chart_product`, `weightedGreen`, `weightedDivZero`, `weightedDivZero_of_connTrace`, `connTraceVec`, `connTraceDivEq`, `RicciFlower.Realized.connTraceField`, `shiftIntEq`, `RicciFlower.LeviCivita.lcGammaVar`, `gammaTraceVar_of_lcGammaVar`, `gammaTraceCovVar`, `lcTraceShifted`, `lcRicciVarCoord`, `lcHessVarCoord`, `lcRicciHessVarCoord`, `lcRicciHessVarShifted`, `RicciFlower.RicciFlow.Perelman.ricciHessianWeightedDivergence_of_ricci_hessian`, `ricciHessianWeightedDensity_of_divergence`, `inverseMetricVariationContractionTermInFrame`, `RicciFlower.Analysis.DivergenceTheorem.expNegLap`, `expNegGreen` | Concrete `F` functional plus tau-free density and moving-volume producers are added. The arbitrary metric-variation coordinate stack remains available as a proof layer with real producers where proved and explicit regularity predicates where not yet produced. The canonical path-based endpoint records the book definition of `delta_(v,h)F(g,f)`. Remaining frontier: fill the theorem-chain bridge from admissible paths and regularity to the checked formula 5.10 assembly. |
| `notes_and_commentary:lbl551`-`lbl552` | `BK.MSM135.Chapter06.Section01.lbl551_entropy_first_variation`, `lbl551_entropy_first_variation_lemma61_of_preIBP`, `lbl551_entropy_first_variation_actual_derivative_of_preIBP`, `lbl551_bracket_variation_producer`, `lbl551_entropy_first_variation_producer_of_volumeVariation`, `lbl552_weighted_ibp` | `RicciFlower.RicciFlow.Perelman.wEntropyBracket_hasDerivAt`, `WEntropyHasFirstVariationAt_of_volumeVariation`, `wEntropyFirstVariation_eq_lemma61_of_hasFirstVariationAt_preIBP`, `weightedIBP` | The scalar bracket derivative, moving-volume base-integral producer, and closed weighted-IBP wrapper are in place. The prior `gradFun_exp_neg` frontier has been proved; measurability/base integrability assumptions remain explicit. |
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
