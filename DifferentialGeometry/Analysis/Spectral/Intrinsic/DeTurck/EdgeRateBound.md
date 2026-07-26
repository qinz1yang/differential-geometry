# EdgeRateBound

## Current source state

`EdgeRateBound.lean` is source-complete for the fixed-time principal and top
formal-partner estimates, with no `sorry`, `admit`, axiom, or opaque
replacement.  A focused Lean check has not yet run: the shared workspace is
coordinating another named build, so every declaration below remains
**source-level, unverified** until the lock-aware check is authorized.

The new source declarations are:

- `edgeRate0` and `edgeRate1`, the exact visible order-zero and order-one
  fields after the Palatini--DeTurck refold;
- `exists_edgePairRef`, which reconstructs the existing refold package while
  retaining `qA`, `qB`, `q`, and `epsilon`.  Those data are essential inputs
  to `edgeTop_zero` and `edgeTop_one`; `exists_edgeSlopeRef` hides them;
- `edgeCore_path_le`, which correctly applies `edgeCore_pair_le` to `s • W`
  and cancels the positive factor `s ^ 2`.  The tempting direct application
  to `W` is invalid because the slope metric is `g + s W`, not `g + W`;
- `edgeTop_pair_le`, which combines `edgeTop_green`, `edgeTop_zero`,
  `edgeTop_one`, and
  `exists_iteratedCovGrad_covDivergence_l2_le`.  It chooses a positive radius
  internally and proves
  `topPair <= (1/4) * ||nabla W||^2 + K * ||W||^2`; and
- `edgePair_pair_le`, which conditionally cancels that positive quarter
  against the negative quarter in `edgeCore_path_le` once pointwise bounds for
  the *entire supplied* `C0` and `C1` fields are already available.  It is
  generic refold glue; it does not produce such bounds for the concrete
  `edgeRate0` and `edgeRate1`.

## Mathematically valid part of the route

The top refold has the required sharp zero.  If `P_s` is the explicit
rank-four formal partner, the existing pointwise producers give

`|P_s|^2 <= C0 * delta^2 * |W|^2`,

`|nabla P_s|^2 <= C1 * delta^2 * |nabla W|^2`.

The public divergence estimate at order zero therefore controls
`||div P_s||` by the sum of these two norms.  Cauchy--Schwarz and Young's
inequality absorb the resulting gradient term after shrinking `delta`; no
`H2` norm of the arbitrary edge tensor is introduced.

The principal route is also faithful.  At slope `s`, the realization theorem
ties the metric to `s • W`.  Homogeneity of the rough Laplacian, principal
arm, lower arm, covariant derivative, and Hilbert pairing gives an exact
factor `s^2`, which is cancellable for `s in (0,1)`.

The moving inverse-metric and volume reactions are not a mathematical gap:
`movingReactVol_le` already provides the required pointwise multiple of the
moving difference norm, and `carrierEdge_bounds` supplies one carrier-speed
constant on a closed slab.

## Routes which do not close the time-uniform edge estimate

1. **Generic coefficient suprema.**  For one fixed smooth `W`, the public
   `joint_jet_bdd` theorem can bound `edgeRate0/1` uniformly in the slope
   variable.  Its constant depends on high spatial jets of that particular
   `W`.  Along a closed-edge time family the available regularity is only
   interior-smooth and edge-continuous, so those constants may diverge as
   `t -> 0+`; they do not produce the single `K` required by
   `movingEnergy_zero`.
2. **Ball-uniform coefficient estimates.**  The canonical ball-uniform APIs
   for the Ricci connection-difference, Riemann, and DeTurck coefficient
   fields all require a finite high-jet radius `R`.  Supplying such an `R`
   would assume the missing edge derivative regularity rather than prove the
   closed-edge estimate.
3. **A standalone `C2` estimate.**  Pairing the refolded top coefficient with
   `nabla^2 W` by a coarse `H2` bound loses the small undifferentiated `W`
   factor.  The formal-partner Green route in `edgeTop_pair_le` is necessary.
4. **Using `exists_edgeSlopeRef` alone.**  That producer existentially hides
   the permutations and signs needed by the sharp partner bounds.  The source
   theorem `exists_edgePairRef` repairs this data-flow issue rather than
   postulating a new coefficient.

## Three independent closure routes audited

The following are genuinely different mathematical routes, not three names
for the same missing estimate.

1. **Direct Palatini/Green integration by parts.**  This is still the faithful
   route.  Expanding `linearizedRicciConnDiffOrder0CLM` shows six terms
   quadratic in `A = connDiff(g_s,g)` and two terms linear in
   `DA = covGrad A`.  The quadratic terms and the order-one arm can retain a
   small undifferentiated `W`; the two `DA` terms must first be moved by
   Green's identity.  The canonical library already supplies
   `tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`, the lowered
   tensor `connDiffLoweredCc`, and the rank-reducing product-rule identities in
   `RankReducingOperatorFieldGreenIBP`.  It also rewrites
   `connDiffGradContrInsertionField` as a reindexed slot extension of
   `covGrad connDiffSection`.  What is not supplied is the exact formal
   adjoint through the *outer* Ricci four-trace and reindex contractions: an
   identity lowering the two `DA` monomials through the outer trace to an
   explicit mixed-trace flux.  A subsequent one-dimensional scaling audit
   rules out the initially proposed use of `edgePairMono`: that operator has
   two moving-metric traces and scales as `m^-2` for `g = 1`, `gm = m`, while
   the actual Ricci four-trace has one and scales as `m^-1`.  The direct route
   therefore needs a new single-moving-trace/base-trace formal partner.  This
   is a local tensor-algebra producer, not a new regularity hypothesis.
2. **Exact Ricci--DeTurck algebraic cancellation.**  `rhsSlope_eq_arms` and
   `RHSThreeArmCancel` cancel the Ricci/DeTurck principal second-order symbols,
   while `LieThreeArmCancel` and the `tail0_decomp` chain cancel the
   self-background differentiated DeTurck tail.  They do not cancel the
   Ricci `DA` arm.  This is visible in the final normal form:
   `edgeRicciHalf` still contains
   `linearizedRicciConnDiffOrder0CoeffField`, and `edgeQuad1` still contains
   `linearizedRicciConnDiffOrder1CoeffField`; `edgeFold0` contains no hidden
   derivative of the connection difference.  No theorem in
   `DifferentialGeometry/` rewrites their signed `L2` sum to zero or to a
   pointwise bounded reaction.
3. **Low-regularity/reverse-Duhamel uniqueness.**  The concrete low-regularity
   coefficient producers close on a spectral endpoint ball: in particular
   `rhs0_h1_of_aux` requires endpoint `H3` control, and `edgePath_strong`
   requires the high-scale spatial and time-derivative `MemLp` data in
   `EdgeStrongData`.  The public forward-uniqueness theorem assumes only joint
   `C0` regularity at the initial edge and joint smoothness for positive time,
   so neither input follows uniformly as `t -> a+`.  The proved
   `metricRD_local` theorem does give Ricci--DeTurck uniqueness on a positive
   window whose left endpoint is already smooth, but it cannot be started at
   the original `C0` edge.  Thus this route needs a new boundary-regularity
   producer (high-scale `MemLp`, or the finite-order `ricciEdgeDeriv` package),
   not a repackaging of the existing strong fixed-point theorem.

Consequently none of the three routes currently closes from the exact public
edge hypotheses.  The first route identifies a local algebraic/analytic
producer and does not indicate that the theorem statement is false; the third
route would instead require a substantially broader initial-edge parabolic
regularity theorem.  The scaling test is also a useful negative result: it
prevents the missing single-trace adjoint from being hidden behind the already
proved two-trace `edgePair_l2` API.

## Exact remaining mathematical producer

The unique smallest analytic gap is the structural visible-lower-arm pairing,
not another coefficient-sup theorem.  A consumer-shaped next lemma is:

`edgeVis_pair_le`

with conclusion, uniformly for every slope,

`<W, edgeLowerArm g (edgeRate0 ...) (edgeRate1 ...) W>`

`<= c * delta * ||nabla W||^2 + K * ||W||^2`,

where `c * delta` is small and `K` depends only on the carrier/background
closed-slab data, not on high jets of the arbitrary edge solution.  Expanded,
the visible fields are

`edgeRate1 = -2 * RicciConnDiff1 + DeTurckLieArm1`,

and

`edgeRate0 = -2 * RicciConnDiff0 - Riemann0 + DeTurckEndo + lieCorr0
  + phiMetCurv + C0`.

Their connection-difference terms must be paired at the energy level so that
derivatives fall on `W` and retain a small undifferentiated metric difference.
Proving separate pointwise suprema is the wrong abstraction boundary.

The first non-packaging child on the direct route is narrower than
`edgeVis_pair_le`.  The new `EdgeRicciPairing.lean` layer now gives concrete
`ricciAAKer`, `ricciDAKer`, `ricciKer_split`, and `ricciCoeff_split`
declarations by reproving the private six-plus-two expansion from public
definitions.  The next identity, `ricciDA_pair`, must construct the genuine
one-trace quadratic flux and rewrite the derivative-arm pairing as its pairing
with `covGrad (connDiffLoweredCc g gm)`.  For symmetric `W`, the eight raw
scalar terms cancel to

`sum W[u,v] * W(L p,r) * (D[u,v,p,r] - D[p,u,v,r])`,

where `L` is the relative inverse-metric endomorphism and
`D[p,u,v,r] = g((nabla_p A)(u,v),r)`.  Thus the concrete flux has components

`P[p,u,v,r] = W[p,u] * W(L v,r) - W[u,v] * W(L p,r)`.

It has exactly one relative inverse-metric insertion and can be assembled
from `edgeProd4`, `edgeSlot2`, and one fixed slot permutation.  The raw
`2 x 4 = 8` expansion is an intermediate verification device, not a sum of
the existing two-trace monomials.

The exact Green theorem `ricciDA_green` should then follow from
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence`.  Its follow-up
estimate `edgeRic_pair_le` must combine the six `A*A` monomials, this
integrated derivative flux, and the Ricci order-one arm; the derivative and
order-one pieces should be audited jointly for their signed cancellations.
The DeTurck sibling `edgeDet_pair_le` should be lower-order: the required
diagonal-zero fibre estimates already occur inside the low-regularity
development, but the sharp Arm1 pieces and sharp-flat/kappa decompositions
needed here are private; the public ball-uniform wrappers add an inadmissible
high-jet radius.  They must be exported or reproved at this energy boundary.
Neither child may be replaced by assuming its desired signed pairing bound.

`EdgeRicciPairing.lean` directly imports
`RicciConnDiffOrder0KernelJetGrid`,
`FlatArmCoeffConnectionDifferenceBridge`, `EdgeRefoldPairing`, and
`RankReducingOperatorFieldGreenIBP`.  The kernel split is now present at
source level without modifying upstream private declarations.  The smallest
remaining public bridge is component-level compatibility between
`covGrad (connDiffLoweredCc g gm)` and the derivative tensor used by
`connDiffGradContrInsertionField`: the bridge file exposes the norm identity
`connLow_rfns`, but keeps its exact realization lemmas private.  This bridge
may be reproved locally; the desired pairing cannot be introduced as a
hypothesis.

There is also a routine but currently unnamed packaging lemma needed after
this estimate: interchange the slope interval integral with the spatial
`L2` pairing in `rhsArm_sub_eq_paths`.  The shortest canonical proof uses
`MeasureTheory.intervalIntegral_integral_swap`, following
`PathIntegralFibreNormTransfer`, on each of the three smooth coefficient arms.
This is an API glue task, not the analytic obstruction.  The raw
`rhsSumSlope` fixed-vector integrability theorem alone is insufficient for the
space--slope Fubini step.

## Honest progress

- Exact `ricci_flow_forward_unique`: **0%** until its existing theorem is
  proved and axiom-checked.
- `EdgeRateBound` fixed-time source machinery: **80% source-level, 0% Lean
  verified** pending the coordinated focused check.
- Closed-edge Ricci--DeTurck rate machinery: the principal and top arms are
  assembled at source level, and the concrete Ricci six-plus-two kernel split
  is written source-only; the single-trace derivative pairing, the remaining
  visible lower-arm estimate, and final space--slope packaging remain.
- `extends_of_rmBounded`: unchanged; it still has both analytic producer
  dependencies.
- The full Hamilton positive-Ricci program: unchanged at theorem level until
  both `ricci_flow_unif_existence` and `ricci_flow_forward_unique` are proved
  without `sorryAx`.
