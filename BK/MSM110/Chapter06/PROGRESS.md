# MSM110 Chapter 6 Progress

Source: `C:/Users/liao9/Downloads/MSM110_clean01.tex`, Chapter 6.

Last updated: 2026-05-15.

Full inventory pass:

- `LABEL_INVENTORY.md` records all 114 labels from `chapter6.tex`.
- `MISSING_DEFINITIONS.md` records the smallest missing vocabulary for labels
  that are not yet clean theorem statements.
- Sections 6.4-6.10 now have exact-label comments in their BK modules and
  statement predicates for the intermediate displayed equations that were
  previously only covered coarsely.

BK is a book companion layer only.  Canonical proofs stay in
`RicciFlower/RicciFlow/Evolution/*`; this file records which book-facing
statements are covered, what theorem they use, and what remains.

Distance scale:

- `0`: native `RicciFlower` theorem is closed and BK exposes the book-facing
  wrapper.
- `1`: theorem is essentially closed, but a book-facing presentation or
  tensor-level wrapper remains.
- `2`: coordinate-frame/component statement is proved, but a trace, producer,
  or packaging step remains.
- `3`: real geometric producer remains, such as a Bianchi, commutator, mixed
  derivative, or metric-to-coordinate regularity theorem.
- `4`: major analytic/global Ricci-flow infrastructure remains.
- `5`: deliberate black box or external-scale theorem for now.

## Section 6.1, Evolution Under Ricci Flow

### Inverse Metric Evolution

Statement:

```text
partial_t g^{ij} = 2 Ric^{ij}
```

Status: closed natively as `RicciFlower.RicciFlow.evol_inverse_metric_inFrame`
and exposed in BK as `eq_inverse_metric_ricci_flow`.  The theorem is a
fixed-frame component statement using the inverse-metric component regularity
package.

Distance: `0`.

Next target: none for the displayed component identity.

### Inverse Metric Spacetime Smoothness Dependency

Statement:

If the frame Gram matrix

```text
G(t,x)_{ij} = g(t)_x(e_i, e_j)
```

is spacetime smooth and `gInv` is its two-sided inverse, then each inverse
component

```text
(t,x) |-> g^{ij}(t,x)
```

is spacetime smooth.

Status: closed natively as `RicciFlower.RicciFlow.gInv_spacetimeSmooth`.  This
is not a separate MSM110 display equation, but it is a key dependency for
deriving Christoffel mixed regularity from metric spacetime smoothness.

Distance: `0`.

Next target: do not revive the deleted local/eventual chart formula.  The
regular-time mixed derivative predicate now exists, so the remaining blocker is
a pointwise coordinate-frame/Koszul producer reusing the already proved
`coordinateFrameAt_bracket_zero_of_mem`.

### Equation `eq:christoffel_symbols_ricci_flow`

Statement:

```text
partial_t Gamma^k_{ij}
  = - g^{k l} (
      nabla_i Ric_{j l}
    + nabla_j Ric_{i l}
    - nabla_l Ric_{i j})
```

Status: closed in fixed-frame component form as
`RicciFlower.RicciFlow.evol_christoffel_inFrame`, exposed in BK as
`eq_christoffel_symbols_ricci_flow`.

Distance: `1`.

Next target: package the needed frame regularity from a smooth Ricci-flow
metric family, instead of passing it explicitly.

### Equation `eq:riemann_curvature_three_one_ricci_flow_one`

Statement:

```text
partial_t R^l_{i j k}
  = g^{l p} (
      - nabla_i nabla_j Ric_{k p}
      - nabla_i nabla_k Ric_{j p}
      + nabla_i nabla_p Ric_{j k}
      + nabla_j nabla_i Ric_{k p}
      + nabla_j nabla_k Ric_{i p}
      - nabla_j nabla_p Ric_{i k})
```

Status: covered as an arbitrary-point coordinate-frame component theorem by
`RicciFlower.RicciFlow.riemann13VariationFormulaInFrameOnLocal_of_christoffelEvolution`,
exposed in BK as `eq_riemann_curvature_three_one_ricci_flow_one_local`.
The `{x0}` singleton is the pointwise coordinate-calculation surface; since
`x0` is arbitrary, locality at one point is not the remaining weakness.  The
conditional input is the fixed-base mixed Christoffel derivative package.  The
displayed `partial Gamma + Gamma Gamma` route is coordinate-frame/bracket-zero;
an arbitrary fixed frame would need the corresponding bracket or structure
coefficient terms.

Distance: `3`.

Next target: derive fixed-base Christoffel mixed regularity from metric
spacetime smoothness, then optionally add a tensor-level book-facing wrapper.

### Equation `eq:ricci_tensor_ricci_flow_one`

Statement:

```text
partial_t Ric_{j k}
  = Delta Ric_{j k}
    + nabla_j nabla_k R
    - g^{p q} (
        nabla_q nabla_j Ric_{k p}
      + nabla_q nabla_k Ric_{j p})
```

Status: locally composed as
`RicciFlower.RicciFlow.ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution`,
exposed in BK as `eq_ricci_tensor_ricci_flow_one_local_from_christoffel`.
It combines the arbitrary-point coordinate-frame Riemann producer with the
local Ricci trace theorem in the coordinate frame at `x0`.

Distance: `2`.

Next target: remove the explicit mixed-Christoffel input by deriving it from
metric spacetime smoothness.  A tensor-level wrapper can be added afterward if
the book-facing interface needs it.

### Equation `eq:ricci_tensor_ricci_flow_two`

Statement:

```text
partial_t Ric_{j k}
  = Delta_L Ric_{j k}
  = Delta Ric_{j k}
    + 2 g^{p q} g^{r s} Rm_{p j k r} Ric_{q s}
    - 2 g^{p q} Ric_{j p} Ric_{q k}
```

Status: proved as fixed-frame implications, exposed in BK by
`eq_ricci_tensor_ricci_flow_two_local` and `eq_ricci_tensor_ricci_flow_two`.
The canonical theorems are
`RicciFlower.RicciFlow.ricciEvolutionEquationInFrameOnLocal_of_variation_commutators`
and `RicciFlower.RicciFlow.evol_ricci_inFrame_of_variation_commutators`.
They still assume the Ricci variation formula and the contracted commutator
reduction.

Distance: `3`.

Next target: prove `RicciContractedCommutatorsInFrame` from the realized
commutator and Bianchi APIs, then connect it to the local variation chain.

### One-Form Ricci Identity Support

Statement:

```text
For a one-form alpha,

  (nabla^2 alpha)(X,Y,Z) - (nabla^2 alpha)(Y,X,Z)
    = - alpha(R(X,Y)Z).

In the realized Rm13 convention this is:

  nabla2Alpha(X,Y,Z) - nabla2Alpha(Y,X,Z)
    = - Rm13(alpha, X, Y, Z).
```

Status: the one-form Ricci identity layer is proved in
`RicciFlower.Tensor.RicciIdentity` and exposed through
`RicciFlower.Connection.RicciIdentity`.  The main handles are
`OneFormThirdCovDerivCommAt`, `one_form_third_comm_of_coord`,
`one_form_third_comm_of_coord_ijk`,
`oneFormRicciIdentity_of_connection`, and
`oneFormRicciIdentity_of_smooth_connection`.  The trace-level consumer
`oneForm_ricci_trace_comm_of_third_comm` is also proved.

This is supporting infrastructure for Bochner/commutator arguments.  It does
not by itself close the Chapter 6.1 Ricci-tensor contracted commutator package
`RicciContractedCommutatorsInFrame`, whose terms involve second derivatives of
the Ricci tensor rather than a general one-form.

Distance: `1`.

Next target: use this layer only where the Chapter 6.1 argument genuinely
reduces to a one-form commutator.  Keep the Ricci-tensor contracted commutator
frontier separate.

### Equation `eq:scalar_curvature_ricci_flow_one`

Statement:

```text
partial_t R
  = 2 Delta R
    - 2 g^{j k} g^{p q} nabla_q nabla_j Ric_{k p}
    + 2 |Ric|^2
```

This is the pre-Bianchi form, before replacing the contracted Ricci-Hessian
term by one half of `Delta R`.

Status: represented as the interface
`RicciFlower.RicciFlow.ScalarPreBianchiEvolutionEquationOn`.  BK consumes it as
an input to `eq_scalar_curv_evolu`.

Distance: `3`.

Next target: derive this pre-Bianchi scalar identity from the Ricci tensor
evolution package after the Ricci commutator frontier is closed.

### Scalar Contracted-Bianchi Algebra

Statement:

```text
g^{j k} g^{p q} nabla_q nabla_j Ric_{k p}
  = (1 / 2) Delta R
```

Status: algebraic bridge closed as
`RicciFlower.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi`,
exposed in BK as `scalar_contracted_bianchi_reduction`.  The theorem consumes
the sharply named hypothesis `ScalarSecondDerivativeContractedBianchiOn`.

Distance: `2`.

Next target: prove `ScalarSecondDerivativeContractedBianchiOn` from the
realized contracted Bianchi identity.

### Equation `eq:scalar_curv_evolu`

Statement:

```text
partial_t R = Delta R + 2 |Ric|^2
```

Status: closed conditionally as
`RicciFlower.RicciFlow.msm110_ch6_1_scalar_curvature_evolution`, exposed in BK
as `eq_scalar_curv_evolu`.  It rewrites the pre-Bianchi scalar evolution using
the scalar contracted-Bianchi reduction.

Distance: `2`.

Next target: replace the pre-Bianchi and Bianchi hypotheses with producers from
the Ricci evolution and realized Bianchi layers.

### Equation `eq:evolution_of_volume_element`

Statement:

```text
partial_t dmu = - R dmu
```

Status: proved in the current integrated moving-measure API as
`RicciFlower.RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar`,
exposed in BK as `eq_evolution_of_volume_element_integrated`.  This proves the
book content after integration against a test function, not yet as a literal
pointwise density derivative.

Distance: `1`.

Next target: add a pointwise density theorem if the volume-density API exposes
the needed time derivative.

### Total Volume Evolution

Statement:

```text
d/dt Vol(M, g(t)) = - int_M R dmu_{g(t)}
```

Status: closed natively as
`RicciFlower.RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv`,
exposed in BK as `total_volume_evolution_ricci_flow`.

Distance: `0`.

Next target: none for the integrated total-volume statement.

## Section 6.2, Uhlenbeck's Trick

### Evolving Frame ODE

Statement:

```text
d/dt e_a(t) = Rc(e_a(t))
d/dt g(t)(e_a(t), e_b(t)) = 0
```

Status: recorded in `RicciFlower.RicciFlow.Evolution.Uhlenbeck` by
`FrameRicciODEInFrameOn`, `MovingFrameGramConstantOn`, and
`evolvingFrameGram_constant_of_ricciFlow`.  The BK wrapper is
`BK.MSM110.Chapter06.Section02.lem_evolving_frame_calculation`.

Distance: `3`.

Next target: prove the product-rule cancellation
`-2 Ric(e_a,e_b) + g(Rc e_a,e_b) + g(e_a,Rc e_b) = 0` from the component
metric/Ricci-endomorphism compatibility hypotheses.

### Orthonormality Preservation

Statement:

```text
if g(0)(e_a(0), e_b(0)) = delta_ab,
then g(t)(e_a(t), e_b(t)) = delta_ab.
```

Status: stated as `evolvingFrame_orthonormal_of_initial`, exposed in BK as
`cor_evolving_frame_orthonormal`.

Distance: `3`.

Next target: prove the interval/ODE consequence from zero derivative of every
Gram component.

### Bundle Isomorphism ODE

Statement:

```text
partial_t iota = Rc o iota
iota(0) = iota_0
```

In components:

```text
partial_t iota_a^k = R_l^k iota_a^l
```

Status: recorded as `BundleIsomorphismODEInFrameOn`, exposed in BK as
`eq_ode_for_bundle_isomorphism`.  The pulled-back metric component

```text
h_ab = g(iota e_a, iota e_b)
```

is recorded by `uhlenbeckPullbackMetricCompInFrame` and
`UhlenbeckPullbackMetricComponents`.

Distance: `2`.

Next target: connect the component ODE to an actual smooth bundle isomorphism
on a vector bundle `V`.

### Equation `eq:uhlenbeck_pullback_of_riemann`

Statement:

```text
R_abcd = (iota^* Rm)(e_a,e_b,e_c,e_d)
       = iota_a^i iota_b^j iota_c^k iota_d^l R_ijkl
```

Status: recorded as `uhlenbeckPullbackRmInFrame` and
`UhlenbeckPullbackRmComponents`, exposed in BK as
`eq_uhlenbeck_pullback_of_riemann`.

Distance: `1`.

Next target: package this with an actual bundle map and local frame on `V`
rather than raw component functions.

### Lemma `lem:uhlenbeck_curvature_evolution_one`

Statement:

```text
partial_t R_abcd
  = Delta_D R_abcd
    + 2 (B_abcd - B_abdc + B_acbd - B_adbc)

B_abcd = h^{e g} h^{f h} R_a e b f R_c g d h
```

Status: recorded as `UhlenbeckCurvatureEvolutionInFrameOn`, with RHS
`uhlenbeckCurvatureEvolutionRHSInFrame` and B-tensor
`uhlenbeckBTensorInFrame`.  The producer theorem
`uhlenbeckCurvatureEvolutionInFrameOn_of_ricciFlow` is present with an
intentional `sorry`, exposed in BK as `lem_uhlenbeck_curvature_evolution_one`
and `eq_rm_evolution_uhlenbeck_trick`.

Distance: `3`.

Next target: prove the cancellation between the four `partial_t iota` product
rule terms and the Ricci-drift terms in the pre-Uhlenbeck Riemann evolution.

## Section 6.3, The Structure of the Curvature Evolution Equation

Section label: `sec:structure_of_curvature_evolution`.

### Curvature Operator on Two-Forms

Statement:

```text
(Rm(U))_ij = - g^{k p} g^{ell q} R_ij k ell U_pq

<U,V> = g^{i k} g^{j ell} U_ij V_k ell
```

Status: recorded in `RicciFlower.RicciFlow.Evolution.CurvatureOperator` as
`curvatureOperatorTwoFormInFrame` and `twoFormInnerProductInFrame`, exposed in
BK by `eq_inner_product_for_wedge_two`.  The self-adjointness assertion is
recorded as `CurvatureOperatorSelfAdjointInFrame`; the producer
`curvatureOperator_selfAdjoint_of_riemann_symmetries` is present with an
intentional `sorry`.

Distance: `2`.

Next target: prove the component self-adjointness calculation from
`Riemann04AlgebraicSymmetriesInFrame`.

### Equation `eq:define_square_of_riemann`

Statement:

```text
(Rm^2)_ij k ell = g^{p q} g^{r s} R_ij p s R_r q k ell
```

Status: recorded as `riemannSquareInFrame` and
`RiemannSquareComponents`, exposed in BK by `eq_define_square_of_riemann`.

Distance: `1`.

Next target: prove the algebraic identity

```text
(Rm^2)_abcd = 2 (B_abcd - B_abdc)
```

from the first Bianchi identity and the existing `B` tensor interface.

### Equation `eq:define_lie_square`

Statement:

```text
(L#)_alpha beta
  = C_alpha^{gamma delta}
    C_beta^{epsilon zeta}
    L_gamma epsilon L_delta zeta
```

Status: recorded as `lieSquareInBasis` and `LieSquareComponents`, exposed in
BK by `eq_define_lie_square`.

Distance: `1`.

Next target: replace the intentional `sorry` in `lieSquare_nonnegative` by the
finite-dimensional diagonalization argument for symmetric nonnegative bilinear
forms.

### Equation `eq:lie_bracket_for_wedge_two`

Statement:

```text
[U,V]_ij = g^{k ell} (U_i k V_ell j - V_i k U_ell j)
```

Status: recorded as `twoFormLieBracketInFrame`, with ordered-pair structure
constants `twoFormStructureConstInFrame`.  The ordered-pair interface avoids
choosing an `i < j` ordering on the abstract finite index type.

Distance: `1`.

Next target: connect the ordered-pair structure constants to the book's
`i < j` wedge basis if a later theorem needs exact basis-level comparison.

### Equation `item:lie_square_of_riemann`

Statement:

```text
(Rm#)_ij k ell
  = R_pq u v R_r s w x
    C_(ij)^(pq,rs) C_(ell k)^(uv,wx)
```

Status: recorded as `riemannLieSquareInFrame` and
`RiemannLieSquareComponents`, exposed in BK by
`item_lie_square_of_riemann`.

Distance: `2`.

Next target: prove the algebraic identity

```text
(Rm#)_abcd = 2 (B_acbd - B_adbc)
```

using the two-form Lie bracket constants and the algebraic identities for `B`.

### Theorem `thm:uhlenbeck_curvature_evolution_two`

Statement:

```text
partial_t (iota^* Rm)
  = Delta_D Rm + Rm^2 + Rm#
```

Status: recorded as `CurvatureOperatorEvolutionInFrameOn`, with RHS
`curvatureOperatorEvolutionRHSInFrame`.  The producer
`uhlenbeckCurvatureEvolution_slick_of_btensor_identities` is present with an
intentional `sorry`; it takes the two algebraic identities relating `Rm^2` and
`Rm#` to the Section 6.2 `B` tensor and rewrites the Uhlenbeck evolution RHS.
BK exposes it as `thm_uhlenbeck_curvature_evolution_two`.

Distance: `3`.

Next target: prove the two algebraic `B`-tensor identities, then the final
rewrite from Section 6.2 should be a short derivative-preservation step.

### Corollary `cor:pc_opreserved`

Statement:

```text
If the curvature operator is positive initially, it remains positive.
If the curvature operator is negative initially, it remains negative.
```

Status: recorded as `positiveCurvatureOperator_preserved_of_slick_evolution`
and `negativeCurvatureOperator_preserved_of_slick_evolution`, exposed in BK by
`cor_pc_opreserved_positive` and `cor_pc_opreserved_negative`.  Both producers
are intentional `sorry`s because this is the tensor maximum-principle
application frontier.

Distance: `4`.

Next target: connect `CurvatureOperatorEvolutionInFrameOn` to the Chapter 4
system/tensor maximum principle once that interface is formalized.

## Deferred Chapter 6 Frontiers

The remaining Chapter 6.1 work is concentrated in a few producer theorems:

- Derive `ChristoffelCoordMixedDerivativeInFrameOn` from metric spacetime
  smoothness, using `gInv_spacetimeSmooth` and the coordinate Christoffel
  formula.
- Optionally promote the arbitrary-point coordinate-frame Riemann and Ricci
  component identities to tensor-level book-facing wrappers.  Do not treat the
  coordinate `partial Gamma + Gamma Gamma` calculation as an arbitrary-frame
  formula unless bracket or structure-coefficient terms are included.
- Prove `RicciContractedCommutatorsInFrame` from the realized commutator and
  Bianchi APIs.  The one-form Ricci identity is already available, but this
  Ricci-tensor package is a separate contracted second-derivative frontier.
- Prove `ScalarSecondDerivativeContractedBianchiOn` from the realized
  contracted Bianchi identity.
- Add the pointwise volume-density formula if the measure/density layer exposes
  the right derivative object.
- Leave tensor maximum-principle applications deferred until the Section 6.1
  evolution identities are stable.
- Prove the Section 6.2 Uhlenbeck product-rule cancellations and connect the
  component statements to a genuine pulled-back vector-bundle connection.
- Prove the Section 6.3 curvature-operator algebra: self-adjointness from
  Riemann symmetries, Lie-square positivity, the two `B`-tensor identities for
  `Rm^2` and `Rm#`, and the tensor maximum-principle preservation corollary.
