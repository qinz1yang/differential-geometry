# RicciFlow LaTeX Theorem Status

This ledger records theorem-level status for the Hamilton notes.  It should
track current theorem names, status, and next frontiers; it should not preserve
daily work logs.

## Current Dashboard

| Area | Status |
| --- | --- |
| Section 3/14 calculus | Mostly native; no longer the main blocker. |
| Section 6 evolution | Core inverse metric, Christoffel, Ricci, scalar, frame Ricci-norm, smooth-solution Ricci-norm data, and the `smoothOfSol` upgrade are native. |
| Section 7 scalar WMP/lower bound | Native consumer path; scalar regularity from smooth solutions is available. |
| Section 9 Ricci preservation | Local algebra, strict initial selectors, theorem-7.5 consumers, canonical Ricci-flow connection/spatial-derivative producers, and the shifted pinching section with tensor-continuity/core-regularity producers are native; the tensor-backed canonical shifted reaction `shiftNAt` and raw adapter `shiftNRaw` have the symmetric null condition checked from first-null geometry, now including the `delta = 0` Ricci-preservation endpoint. The direct shifted parabolic producer is checked as `pinchParabolic`; barrier reaction regularity is checked as `pinchBarrierReg`, `PinchFlowWMPData.ofShiftNClosed` assembles the shifted WMP data from smooth Ricci-flow hypotheses, `ricci_nonneg_sol_closed` proves Ricci nonnegativity from the `delta = 0` endpoint, and `ham3_pinch9` / `ham3_rescaled_ric_nonneg` wire the solution-level Section 9 packages into the Hamilton endpoint layer. |
| Section 10 pinching | Lemma 10.4 is checked; Lemma 10.5 has checked positive-region and `alpha = 1`, `phi >= 0` side forms, but not the full book-facing hypothesis shape. Lemma 10.6 has checked raw quotient setup, book RHS rewrite, actual tensor-square setup, section-level mixed bridge, canonical solution-section packaging, and the book-facing `pinchEvol_book` theorem. The native estimate interface is present in `ImprovedPinching/Estimate.lean`; the unordered eigenvalue bridge from Section 9 to the Lemma 10.8 reaction sign is checked, the book RHS is bounded by the drift term, the drifted subsolution inequality is checked as `pinchQuotient_parabolic_nonpos`, the compact initial bound is checked, the coordinate-local slab continuity producer for `fun p => ricciNorm S p.1 p.2` is checked, and `pinchEstimate_sol` is checked. `ham3_pinch_imp_can` exposes the canonical carrier estimate as `Ham3PinchEstimate`; `ham3_pinch_imp` remains the display wrapper. |
| Section 11/12 global flow | Global analytic and compactness black boxes remain. |

## Active Native Frontiers

- Section 11/12 global inputs: normalized maximal-flow existence, no-local
  collapsing, Hamilton--Cheeger--Gromov compactness, convergence transfer to
  the limit, scalar strong maximum principle on the complete limit flow, and
  final topological handoff.

## Closed Or Stable Native Results

- Inverse metric evolution: `RicciFlow.evol_inverse_metric_inFrame`.
- Smooth solution upgrade: `RicciFlow.smoothOfSol`.
- Christoffel evolution: fixed local-frame component theorem.
- Ricci evolution and Lichnerowicz component consumers.
- Scalar evolution: `scalarEvolOfSmooth`.
- Ricci norm evolution: canonical frame route through `(0,2)` tensor
  Bochner/product rule and `ricci_heat_mc`.
- Scalar WMP and scalar lower bound consumers.
- 3D Riemann-from-Ricci component algebra and Ricci eigenbasis selection.
- Levi-Civita one-form Ricci identity and scalar Bochner producers.
- `(0,s)` and mixed Ricci identity component algebra.

## Detailed Ledger

### Theorem 2.1, `thm:main-hamilton-3d`

Status: theorem-shaped endpoint exists in `HamiltonPositiveRicci.lean`, but it
still consumes global Section 12 producers.

Distance: `4`.

Next target: replace Section 12 endpoint assumptions one producer at a time.

### Assumption 3.1, `ass:riemannian-calculus`

Status: native lookup map.  Local tensor, coordinate, Levi-Civita, curvature,
and Bochner endpoints exist across RicciFlower files.

Distance: `0`.

Next target: maintain this as a map, not as one monolithic theorem.

### Black Boxes 4.2, 5.1

Status: short-time existence and maximal-flow interval remain global analytic
black boxes.

Distance: `5`.

Next target: only open these when DeTurck/parabolic PDE infrastructure is a
goal.

### Lemmas 6.1-6.7

Status: inverse metric, Christoffel, Ricci, scalar, frame Ricci-norm, and
smooth-solution Ricci-norm data routes have native checked consumers.
`ricciHeatDataSmooth` is now a checked assembly from the strengthened
`IsSmoothSolutionOn` fields, and `smoothOfSol` derives those fields from the
minimal metric solution predicate `IsSolutionOn`.

Distance: `0` for the existing endpoints.

Next target: reuse these producers for trace-free Ricci norm instead of
reopening Ricci norm algebra.

### Theorems 7.1-7.4

Status: scalar WMP and scalar lower-bound/finiteness consumers are native.
`scalarRegOfSmooth` supplies the regularity package from smooth solutions.

Distance: `0` for the scalar route.

Next target: optional convenience wrappers only.

### Theorem 7.5 and Black Box 7.6

Status: tensor WMP now has a checked section-backed certificate route in
`MaximumPrinciple/TensorWeak.lean`.  The local first-null scalar signs are
produced from the selected section derivatives by `strictCert_sec`,
`wmp_section_sec` is the abstract producer endpoint, and `tensor_wmp` is the
LaTeX-facing packaged theorem 7.5 entry.  Scalar strong MP remains a global
analytic black box for blow-up limits.

Distance: `0` for theorem 7.5, `5` for black box 7.6.

Next target: keep Ricci-flow application producers separate from theorem 7.5;
feed section regularity, spatial derivatives, parabolic inequality, and null
condition into `wmp_section_sec` from the appropriate application layer.

### Lemmas 8.1, 10.7, 10.8

Status: dimension-three algebra and eigenvalue inequalities are native.
The post-10.6 reaction-sign context is also native:
`DimensionThree.PinchEigen3.q_sub_nonneg` packages Lemma 10.8 as
`Q - epsilon |Ric|^2 |Ric^o|^2 >= 0` under the ordered nonnegative
eigenvalue context, `delta * R <= l3`, and `epsilon <= 2 * delta^2`.
`RicciFlow.cubicQ_pinchOn` translates that sign into the `cubicQAt` notation
used by Hamilton's Lemma 10.6.

Distance: `0`.

Next target: produce the pointwise `EigenPinchCtxOn` package from Ricci-flow
positivity/pinching data and consume the reaction sign in the post-10.6
differential inequality.

### Lemmas 9.1-9.3

Status: conditional native setup exists for preservation and strict positivity
via local algebra and unit-tangent compactness.  Lemma 9.1 and Lemma 9.2 now
have section-backed consumers through `ricci_nonneg_wmp` and
`ricci_pinch_wmp`, both consuming the generic `TensorWMPInput` package.
Corollary 9.3 has a section-backed conditional route through `PinchWMPData`.
The canonical Ricci-flow producers for theorem-7.5 connection and spatial
derivative fields are checked: `ricciCov1`, `ricciCovInf`,
`ricciMetricComp`, `ricciNablaWMP`, `ricciNabla2WMP`, and
`ricciSpatialWMP`.  The shifted pinching section is now checked as
`pinchSec`, with `pinchSec_eq`, explicit derivative fields
`pinchNablaModel` / `pinchNab2ModelSec`, and tensor-continuity producers
`pinchSecFamilyContinuousOnSet`, `pinchSec_tangentBundle_cont`, and
`pinchSec_tensorQuadCont`.  The strict selector route is checked through
`PinchInitLt`, `pinchInitLt_*`, `pinch_init_wmp_lt`, and
`strict_pinch_*_lt`.  The strict shifted-null eigenvalue algebra is checked by
`shiftScal3_eq`, `shiftNull3`, `pinchShiftNull_ge`, and the compact target
`shiftReact3_nonneg`.  The off-diagonal first-null block algebra is checked
through `stdRmOfRic3`, `shiftBlockS3`, `shiftRicBlock3`,
`shiftReactBlock3_eq`, and `shiftReactBlock3_nonneg`.  Section-core
regularity for the shifted section is now checked through `ricciAt_symm`,
`ricciSec_symm`, `pinchSec_symm`, `pinchSecCore`, and
`PinchFlowWMPData.ofBarrier`; this fills compactness and continuity fields from
smooth solution data once the analytic `TensorBarrierRegularityOn` input is
supplied.  The TensorWeak null predicates now require symmetric bilinear PSD
inputs.  `PinchFlowWMPData.ofSymmNull` adapts the natural symmetric-input null
condition to the legacy raw WMP field when the reaction ignores skew input.
`RicciWMPData.toInput`
builds the Ricci `TensorWMPInput` package, `PinchWMPData.toInput` /
`PinchWMPData.preserve` make the general pinching package reusable, and
`PinchFlowWMPData` fills the canonical shifted section, connection, explicit
derivative fields, and checked `TensorSpatialDerivs` proof.

Distance: `0`.

Next target: use the Section 9 package as an input to the later improved
pinching estimates; the Section 9 WMP data itself is closed.
The reaction-wide null-eigenvector condition is checked through
`NullOrthonormalBasis3At`, `exists_nullOrthonormalBasis3At`, and
`shiftNRaw_null_symm`, with `PinchFlowWMPData.ofShiftN` consuming it at the
application layer.  The direct parabolic route is checked as `pinchParabolic`:
`ricciQuadDeriv_coord` lifts coordinate Lemma 6.3 to arbitrary quadratic Ricci
evaluations, `pinchQuadDeriv_coord` combines it with scalar and metric
evolution, `ricciRoughTrace_coord` and `scalarHessTrace_eq_lap` identify the
heat side, `ricciActualReactAt` and `ricciCoordReact_eq_actual` identify the
coordinate reaction, and `shiftNRaw_pinchCoordReact` closes the canonical
reaction bridge using the actual signed `Rm04` versus `rm04OfRic3At`
convention theorem.  `PinchFlowWMPData.ofShiftNDirect` feeds this checked
parabolic assembly into the canonical shifted WMP package.  The old canonical
shifted `pinchNabla*`
route has been removed from the WMP path; the checked file uses
`pinchNablaModel` / `pinchNab2ModelSec`, with `pinchSpatialModel` proving
their `TensorSpatialDerivs` input.  `pinchSmallLip` proves the canonical
small-barrier reaction control, `pinchBarrierReg` fills the full
`TensorBarrierRegularityOn` package, and
`PinchFlowWMPData.ofShiftNClosed` assembles null condition, direct parabolic
inequality, spatial derivative realization, and barrier regularity from
smooth Ricci-flow data.
The solution-level wrappers `pinch_sol_closed`, `pinch_init_sol_lt`, and
`strict_pinch_sol_lt` now consume the closed package.  The generalized
`delta = 0` path `pinch_sol_closed_nonneg` / `ricci_nonneg_sol_closed` proves
Ricci nonnegativity from the same WMP machinery.  In the Hamilton endpoint,
`HamiltonPositiveRicci.ham3_pinch9_fixed` now keeps one selected Section 9
pinching constant across all compact subintervals, `ham3_pinch9` is its
compatibility projection, and `HamiltonPositiveRicci.ham3_rescaled_ric_nonneg`
converts the original-flow Ricci nonnegativity into the selected rescaled slab
package.

### Lemma 10.4, `lem:evol-tracefree-ricci-norm`

Status: checked consumer stack exists in
`RicciFlow/Evolution/ImprovedPinching.lean`.  `tfHeat_metric_smooth` handles
canonical metric curvature and internal order-one Levi-Civita smoothness.
`tfHeat_book` is the smooth-solution book-facing wrapper, and `tfHeat_sol`
is the base `IsSolutionOn` endpoint via `smoothOfSol`.

Distance: `0`.

Remaining frontier: none for Lemma 10.4 itself.  The next Section 10 work is
the Hamilton quotient specialization and pinching producer layer.

### Lemmas 10.5-10.9

Status: Lemma 10.5 now has native book-facing wrappers in
`RicciFlow/Evolution/ImprovedPinching.lean`.  `quotHeat_book` packages the
general positive-region quotient identity, `quotHeat1_book` packages the
Hamilton-ready `alpha = 1`, `0 <= phi`, `0 < psi` side theorem, and
`quotHeatDiv` gives the `/ psi^beta` display RHS on the positive-denominator
region.  The old local-pinching `PAlphaOverQBetaFormulaOn` surface remains only
a side consumer, not a home for general theorem content.  Q-factorization and
lower-bound eigenvalue algebra are native.

Lemma 10.6 has a checked raw quotient-evolution setup and a checked conditional
book-RHS rewrite.  `tfHeatTerm`, `scalarHeatTerm`, `PinchEvolOn`, and
`pinchEvol_setup` specialize the quotient identity to
`|Ric0|^2 / R^(2 - epsilon)` using Lemma 10.4 and scalar evolution inputs.
`pinchDrift_exp` proves the drift expansion, and `pinchRHS_eq_book` /
`pinchEvol_book_of_couple` rewrite the raw RHS to Hamilton's book RHS once the
tensor-square expansion for `|R ∇Ric - dR ⊗ Ric|^2` is supplied.  The actual
tensor-square setup is now partially checked: `ricciGradCoupleSq_exp_inner`
expands the square to the raw mixed contraction, `ricciGradCoupleSq_exp_mixed`
rewrites it under the mixed-gradient bridge, and `pinchEvol_book_of_mixed`
uses the real `ricciGradCoupleSq` term rather than an arbitrary supplied square
function.  The mixed bridge itself is now checked at the section-realization
level through `ricciMixed_eq_gradNorm`, `ricciMixed_eq_tfGrad`, and
`pinchEvol_sec`.  The canonical section packaging is also checked:
`ricciNablaSec`, `ricciNormDuSec`, `pinchCoupleSol`, and
`pinchEvol_solSec` remove the manual Ricci section, `nabla Ric`,
`du |Ric|^2`, inverse-basis, and norm-identification inputs.  The
base-solution theorem `pinchEvol_sol` also assembles `PinchEvolOn` from
`tfHeat_sol`, `scalarEvolOfSol`, and `pinchEvol_setup`, and produces
`|Ric^o|^2 >= 0`, spatial differentiability of `|Ric^o|^2` and `R`, and the
needed gradient-field differentiability inputs.  Its only remaining explicit
geometric region hypothesis is `R > 0`.  The cleanup theorem `pinchEvol_book`
adds the book assumptions `0 < epsilon < 1` and forwards to `pinchEvol_sol`.

Distance: `0-1`.

The 10.7/10.8 reaction-sign input for the 10.6 reaction term is now checked
through `DimensionThree.PinchEigen3.q_sub_nonneg`,
`DimensionThree.PinchEigen3Unordered.q_sub_nonneg`, and the pointwise
Section-9 bridge `cubicQ_sub_nonneg_of_section9_point`.  The estimate layer
also has checked scalar sign consumers:
`cubicQ_sub_nonneg_of_section9`, `pinchBookRHS_le_drift_sol`,
`pinchDriftVector`, and `pinchEstimateOn_of_pinchQuotient_bound`.

The drifted scalar subsolution inequality, compact initial maximum,
positive-time quotient spatial regularity, scalar WMP sign-change, slab WMP
consumer, coordinate-local Ricci-norm slab continuity, and final
quotient-estimate assembly are checked through
`pinchQuotient_parabolic_nonpos`, `pinchQuotient_initial_bound`,
`pinchQuotient_space_pos`, `pinchQuotient_grad_pos`,
`Realized.parabolic_const_sub`, `pinchQuot_slab_bound`, `ricciNorm_slabCont`,
and `pinchEstimate_sol`.
The full arbitrary-exponent book-facing 10.5 statement under only nonnegative
numerator hypotheses remains unproved and should not be claimed.

Section 9 shifted pinching now has a checked first-null block producer:
`ShiftBlockAt`, `raw_null_of_smul`, and `shiftBlockOfNull` prove that a raw
symmetric bilinear PSD tensor has the expected shifted first-null block
components in any supplied orthonormal basis whose first vector normalizes the
nonzero null direction.  The tensor-backed compatibility layer is checked:
`Tensor02RealizesRawAt` and `tensor02OfRawAt` bundle raw bilinear evaluators,
`Tensor02ReactionAt.toRawSymm` adapts tensor-backed reactions to the legacy raw
WMP API, and `shiftNullSymm_of_block_scaled` handles the `r^2` scaling for
arbitrary null vectors.  The basis-local tensor model `shiftNAtBasis` now
bundles the finite shifted reaction components in a supplied orthonormal basis,
and `shiftNAtBasis_comp_shiftBlock` realizes `shiftReactBlock3` for first-null
blocks.  `shiftNBasisScaled` adds the checked `r^2` scaling for arbitrary null
vectors proportional to the adapted first basis vector.  The canonical
reaction is now also tensor-backed and basis-independent: `ricciReaction3At`,
`shiftNAt`, `shiftNRaw`, `shiftNAt_comp_orthonormal`,
`shiftNAt_comp_shiftBlock`, `shiftNRaw_realizes_block`, and `shiftNScaled`
identify the invariant reaction with the same shifted first-null block target.
The adapted first-null basis and symmetric null predicate are now checked by
`NullOrthonormalBasis3At`, `exists_nullOrthonormalBasis3At`, and
`shiftNRaw_null_symm`; `PinchFlowWMPData.ofShiftN` packages the canonical
shifted reaction for the WMP application.  The direct parabolic input is now
checked by `pinchParabolic`, and `PinchFlowWMPData.ofShiftNDirect` packages
it with the canonical null producer.  The barrier regularity input is now
checked by `pinchBarrierReg`, and `PinchFlowWMPData.ofShiftNClosed` removes
the external `hbar` assumption for the shifted WMP data package.

### Lemmas 11.1-11.6

Status: finite-time, scalar blow-up, and point-selection consumers are native.
The checked `ham3_scalar_blowup` route is noncircular: maximal-endpoint
curvature blow-up is converted to scalar blow-up using Section 9 Ricci
nonnegativity and the dimension-three curvature-control estimate.  The checked
`ham3_point_select` route chooses compact-slab scalar maxima above levels
tending to infinity, giving normalized rescaled scalar curvature and backward
slab scalar bounds.  The later rescaling/noncollapsing/compactness packages
still depend on global producer assumptions.

Distance: `0-4`.

Next target: keep the checked Lemma 11.6 point-selection package separate from
the remaining global noncollapsing, compactness, and limit-geometry inputs.

### Black Boxes 11.8, 11.10, 11.12, 11.14

Status: no-local-collapsing, CGH convergence/compactness, and Myers remain
global inputs.  The non-black-box part formerly hidden in
`ham3_limit_const_metric` has been split into named Section 12 frontiers:
`limit_inherit`, `limit_scal_pos`, `limit_tf_zero`, `limit_const_pos`, and
`limit_to_orig`.  The limit constant-curvature path now explicitly includes
connectedness, boundarylessness, and the three-dimensional rank input, and
`HamiltonPositiveRicci.limitEinstein_of_tf0` checks the pointwise bridge
`|Ric^o|^2 = 0 -> Ric = (R / 3)g`.  The project curvature convention now uses
standard lowered-curvature slots for the bundled user-facing `Rm04`:
`Rm04(X,Y,Z,W) = <R(X,Y)Z,W>`, and `ConstPosSecMetric` uses the sectional
numerator `Rm04(X,Y,Y,X)`.  The local 3D Schur/space-form step is now
checked: `limit_const_sec_of_einstein` turns a connected boundaryless
Einstein limit metric with positive scalar into `ConstPosSecMetric`, and
`const_pos_of_tf0` / `limit_const_pos` are checked wrappers over it.
`limit_tf_zero` is also now checked as an order-closure step from
`LimitTfDecay`.  The theorem `limit_tf_decay` is now a checked consumer of the
explicit CGH/pinching transfer datum `Ham3PinchTransfer`; the remaining
producer work is to prove that datum from CGH pullback convergence plus the
rescaled improved pinching estimate.  The HCG layer has the generic
order-closure bridge `FunctionPullbackTendsto.le_of_bound0`.
`limit_ric_nonneg` is now a checked consumer of the explicit CGH Ricci-transfer
datum `Ham3RicNonnegTransfer`, and `limit_inherit` is checked as an assembly
theorem over the narrower transfer data.  `limit_scal_pos` is now
checked as assembly from the checked scalar-nonnegativity bridge
`limit_scalar_nonneg` and the narrower scalar strong maximum-principle
frontier `limit_scal_pos_smp`.

Distance: `5`.

Next target: decide which of the remaining split limit-transfer frontiers
should be opened first; `Ham3PinchTransfer` is the pinching-to-limit
convergence producer, while `Ham3RicNonnegTransfer`,
`Ham3LimitBaseScalarConv`, and `limit_to_orig` depend on a real CGH
convergence relation.
`limit_scal_pos_smp` is the scalar strong maximum-principle frontier.
`limit_inherit`, `limit_scal_pos`, `limit_tf_decay`, `limit_tf_zero`, and
`limit_const_pos` are no longer local geometry frontiers.

### Appendix Section 14

Status: tensor calculus and local-coordinate appendix statements are mostly
closed natively.  Remaining work is presentation wrappers, not foundational
tensor calculus.

Next target: only package book-facing wrappers when they simplify downstream
Hamilton proofs.

## Near-Term Work Queue

1. Continue from Hamilton quotient equality to the pinching estimates.
2. Leave global analytic/compactness assumptions explicit.
