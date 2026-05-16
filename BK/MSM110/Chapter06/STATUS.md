# MSM110 Chapter 6 Status

Source: `RicciFlow/RicciFlowBooksLatex/MSM110/tex/MSM110/chapters/chapter6.tex`.

Full-label inventory: `BK/MSM110/Chapter06/LABEL_INVENTORY.md` records all
114 Chapter 6 labels and classifies each as a proved wrapper, statement
scaffold with intentional `sorry`, definition-only placeholder, or blocked by
missing vocabulary.

Missing-definition report:
`BK/MSM110/Chapter06/MISSING_DEFINITIONS.md` records the smallest vocabulary
frontiers for labels that cannot yet be typed cleanly as theorem statements.

## Section 6.1 Ricci-Flow Evolution Equations

| LaTeX label | BK wrapper | Canonical RicciFlower theorem | Status |
| --- | --- | --- | --- |
| Ricci-flow inverse metric specialization | `BK.MSM110.Chapter06.Section01.eq_inverse_metric_ricci_flow` | `RicciFlower.RicciFlow.evol_inverse_metric_inFrame` | Proved in fixed-frame component form from the inverse-metric component regularity package. |
| `eq:christoffel_symbols_ricci_flow` | `BK.MSM110.Chapter06.Section01.eq_christoffel_symbols_ricci_flow` | `RicciFlower.RicciFlow.evol_christoffel_inFrame` | Proved in fixed-frame component form from spacetime-smooth metric components and the Ricci-flow metric equation. |
| `eq:riemann_curvature_three_one_ricci_flow_one` | status entry; old wrapper removed | coordinate-frame Christoffel/Ricci variation chain | The regular-time mixed-Christoffel predicate exists. The deleted chart-facing `eventually` route was the wrong surface; the next RicciFlower target is a pointwise coordinate-frame/Koszul producer reusing `coordinateFrameAt_bracket_zero_of_mem`. |
| `eq:ricci_tensor_ricci_flow_one` | `BK.MSM110.Chapter06.Section01.eq_ricci_tensor_ricci_flow_one_local_from_christoffel` | `RicciFlower.RicciFlow.ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution` | Arbitrary-point coordinate-frame Ricci variation is composed from Christoffel evolution and the local Riemann trace, again conditional on the mixed-Christoffel input. |
| `eq:ricci_tensor_ricci_flow_two` | `BK.MSM110.Chapter06.Section01.eq_ricci_tensor_ricci_flow_two_local` and `BK.MSM110.Chapter06.Section01.eq_ricci_tensor_ricci_flow_two` | `RicciFlower.RicciFlow.ricciEvolutionEquationInFrameOnLocal_of_variation_commutators` and `RicciFlower.RicciFlow.evol_ricci_inFrame_of_variation_commutators` | Proved in local and global fixed-frame component forms, assuming the Ricci variation formula and contracted commutator reduction. |
| one-form Ricci identity support | no BK equation wrapper; recorded in progress notes | `RicciFlower.Connection.oneFormRicciIdentity_of_connection`, `RicciFlower.Connection.oneFormRicciIdentity_of_smooth_connection`, and `RicciFlower.Realized.oneForm_ricci_trace_comm_of_third_comm` | Proved as one-form commutator/trace infrastructure. It still leaves the Ricci-tensor contracted commutator package for Chapter 6.1 as a separate frontier. |
| `eq:scalar_curvature_ricci_flow_one` | input hypothesis to `BK.MSM110.Chapter06.Section01.eq_scalar_curv_evolu` | `RicciFlower.RicciFlow.ScalarPreBianchiEvolutionEquationOn` | Recorded as the pre-Bianchi scalar evolution interface. |
| scalar contracted-Bianchi algebra | `BK.MSM110.Chapter06.Section01.scalar_contracted_bianchi_reduction` | `RicciFlower.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi` | Proves the algebraic reduction from the second-derivative contracted-Bianchi trace `Q = (1/2) ΔR`. |
| `eq:scalar_curv_evolu` | `BK.MSM110.Chapter06.Section01.eq_scalar_curv_evolu` | `RicciFlower.RicciFlow.msm110_ch6_1_scalar_curvature_evolution` | Proved from the pre-Bianchi scalar evolution plus the contracted-Bianchi reduction. |
| `eq:evolution_of_volume_element` | `BK.MSM110.Chapter06.Section01.eq_evolution_of_volume_element_integrated` and `BK.MSM110.Chapter06.Section01.total_volume_evolution_ricci_flow` | `RicciFlower.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar` and `RicciFlower.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv` | Proved in the current measure-integrated API. This is not yet a literal pointwise density theorem. |

## Section 6.2 Uhlenbeck's Trick

| LaTeX label | BK wrapper | Canonical RicciFlower theorem or interface | Status |
| --- | --- | --- | --- |
| `eq:e_a_evolution_equation` | `BK.MSM110.Chapter06.Section02.eq_e_a_evolution_equation` | `RicciFlower.RicciFlow.FrameRicciODEInFrameOn` | Statement recorded as the component ODE `partial_t e_a^k = Rc_l^k e_a^l`. |
| `lem:evolving_frame_calculation` | `BK.MSM110.Chapter06.Section02.lem_evolving_frame_calculation` | `RicciFlower.RicciFlow.evolvingFrameGram_constant_of_ricciFlow` | Statement scaffold with intentional `sorry`; it is the product-rule cancellation showing the moving-frame Gram matrix is time-constant. |
| orthonormal-frame corollary | `BK.MSM110.Chapter06.Section02.cor_evolving_frame_orthonormal` | `RicciFlower.RicciFlow.evolvingFrame_orthonormal_of_initial` | Statement scaffold with intentional `sorry`; it packages the Gram-constant lemma into preservation of orthonormality. |
| `eq:ode_for_bundle_isomorphism` | `BK.MSM110.Chapter06.Section02.eq_ode_for_bundle_isomorphism` | `RicciFlower.RicciFlow.BundleIsomorphismODEInFrameOn` | Statement recorded as the bundle-map component ODE `partial_t iota_a^k = R_l^k iota_a^l`. |
| Uhlenbeck isometry claim | `BK.MSM110.Chapter06.Section02.claim_uhlenbeck_bundle_isometry` | `RicciFlower.RicciFlow.uhlenbeck_pullbackMetric_constant_of_ricciFlow` | Reuses the moving-frame Gram statement for the pulled-back metric components. |
| `eq:uhlenbeck_pullback_of_riemann` | `BK.MSM110.Chapter06.Section02.eq_uhlenbeck_pullback_of_riemann` | `RicciFlower.RicciFlow.UhlenbeckPullbackRmComponents` | Component pullback identity recorded as a predicate. |
| `lem:uhlenbeck_curvature_evolution_one` | `BK.MSM110.Chapter06.Section02.lem_uhlenbeck_curvature_evolution_one` | `RicciFlower.RicciFlow.uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow` | Statement scaffold with intentional `sorry`; remaining proof is the Uhlenbeck product-rule cancellation against the Ricci-drift terms. |
| `eq:rm_minus_evolution_minus_uhlenbeck_trick` | `BK.MSM110.Chapter06.Section02.eq_rm_evolution_uhlenbeck_trick` | `RicciFlower.RicciFlow.UhlenbeckCurvatureEvolutionInFrameOn` | Book-facing alias for the final pulled-back curvature evolution equation. |

## Section 6.3 Curvature Operator Structure

| LaTeX label | BK wrapper | Canonical RicciFlower theorem or interface | Status |
| --- | --- | --- | --- |
| `eq:inner_product_for_wedge_two` | `BK.MSM110.Chapter06.Section03.eq_inner_product_for_wedge_two` | `RicciFlower.RicciFlow.twoFormInnerProductInFrame` | Formula recorded. |
| curvature-operator self-adjointness | `BK.MSM110.Chapter06.Section03.curvature_operator_self_adjoint` | `RicciFlower.RicciFlow.curvatureOperator_selfAdjoint_of_riemann_symmetries` | Statement scaffold with intentional `sorry`; needs the component algebra from Riemann symmetries. |
| `eq:define_square_of_riemann` | `BK.MSM110.Chapter06.Section03.eq_define_square_of_riemann` | `RicciFlower.RicciFlow.riemannSquareInFrame`, `RicciFlower.RicciFlow.RiemannSquareComponents` | Formula recorded. |
| `eq:define_lie_square` | `BK.MSM110.Chapter06.Section03.eq_define_lie_square` | `RicciFlower.RicciFlow.lieSquareInBasis`, `RicciFlower.RicciFlow.LieSquareComponents` | Formula recorded. |
| Lie-square nonnegativity lemma | `BK.MSM110.Chapter06.Section03.lem_lie_square_nonnegative` | `RicciFlower.RicciFlow.lieSquare_nonnegative` | Statement scaffold with intentional `sorry`; needs finite-dimensional diagonalization of a symmetric nonnegative bilinear form. |
| `eq:lie_bracket_for_wedge_two` | `BK.MSM110.Chapter06.Section03.eq_lie_bracket_for_wedge_two` | `RicciFlower.RicciFlow.twoFormLieBracketInFrame` | Formula recorded with ordered-pair structure constants. |
| `item:lie_square_of_riemann` | `BK.MSM110.Chapter06.Section03.item_lie_square_of_riemann` | `RicciFlower.RicciFlow.riemannLieSquareInFrame`, `RicciFlower.RicciFlow.RiemannLieSquareComponents` | Formula recorded. |
| `thm:uhlenbeck_curvature_evolution_two` | `BK.MSM110.Chapter06.Section03.thm_uhlenbeck_curvature_evolution_two` | `RicciFlower.RicciFlow.uhlenbeckCurvatureEvolution_slick_of_btensor_identities` | Statement scaffold with intentional `sorry`; needs the `Rm^2` and `Rm#` identities in terms of the Uhlenbeck `B` tensor. |
| `cor:pc_opreserved` | `BK.MSM110.Chapter06.Section03.cor_pc_opreserved_positive`, `BK.MSM110.Chapter06.Section03.cor_pc_opreserved_negative` | `RicciFlower.RicciFlow.positiveCurvatureOperator_preserved_of_slick_evolution`, `RicciFlower.RicciFlow.negativeCurvatureOperator_preserved_of_slick_evolution` | Statement scaffold with intentional `sorry`; this is the tensor maximum-principle application frontier. |

## Sections 6.4-6.10 Statement Inventory

Sections 6.4-6.10 now follow the same book-companion pattern: each section has
one `RicciFlower.RicciFlow.Evolution.*` statement file and one thin
`BK.MSM110.Chapter06.SectionNN` wrapper file.  Intermediate displayed
equations are represented by small predicates where a full tensor or analytic
definition is not yet available.

| Range | BK module | Canonical RicciFlower file | Status |
| --- | --- | --- | --- |
| 6.4 | `BK.MSM110.Chapter06.Section04` | `RicciFlower.RicciFlow.Evolution.OdeReduction` | All labels recorded; algebra/ODE wrappers only. |
| 6.5 | `BK.MSM110.Chapter06.Section05` | `RicciFlower.RicciFlow.Evolution.LocalPinching` | All labels recorded; pinching theorem producers intentionally scaffolded. |
| 6.6 | `BK.MSM110.Chapter06.Section06` | `RicciFlower.RicciFlow.Evolution.ScalarGradient` | All labels recorded; Bochner/gradient-estimate producers intentionally scaffolded. |
| 6.7 | `BK.MSM110.Chapter06.Section07` | `RicciFlower.RicciFlow.Evolution.LongTimeExistence` | All labels recorded; BBS and continuation inputs are explicit frontiers. |
| 6.8 | `BK.MSM110.Chapter06.Section08` | `RicciFlower.RicciFlow.Evolution.FiniteTimeBlowup` | All labels recorded; finite-time singularity and convergence claims are scaffolds. |
| 6.9 | `BK.MSM110.Chapter06.Section09` | `RicciFlower.RicciFlow.Evolution.NormalizedFlow` | All labels recorded; normalized-flow scaling and global comparison remain interfaces. |
| 6.10 | `BK.MSM110.Chapter06.Section10` | `RicciFlower.RicciFlow.Evolution.ExponentialConvergence` | All labels recorded; exponential convergence remains a global analytic frontier. |

## Deferred Frontiers

- The remaining Chapter 6.1 displays are now present as book-facing component
  scaffold statements in `BK.MSM110.Chapter06.Section01`, with `sorry` marking
  the future producer proofs.
- Deriving the scalar second-derivative contracted-Bianchi trace from the current realized Bianchi API.
- Proving the full `RicciContractedCommutatorsInFrame` package from the realized commutator/Bianchi API. The one-form Ricci identity is already available, but this Ricci-tensor contracted package is separate.
- Deriving fixed-base Christoffel mixed-derivative regularity from manifold-level spacetime smoothness.
- Optionally promoting the arbitrary-point coordinate-frame Riemann/Ricci component identities to tensor-level book-facing wrappers with the MSM110 sign and slot conventions.
- Adding arbitrary-frame versions only with the required bracket or structure-coefficient terms.
- Proving the Section 6.2 Uhlenbeck product-rule cancellations and connecting the component statements to a genuine pulled-back vector-bundle connection.
- Proving the Section 6.3 curvature-operator algebra and tensor maximum-principle application.
- Deriving the three-dimensional Ricci reaction formula from the Riemann decomposition.
- Applying tensor maximum principles to Ricci positivity.
