# EdgeRefoldPairing

## Current state

Source assembly is present in `EdgeRefoldPairing.lean`; a focused Lean check is
still pending because the shared worktree currently has a coordinated named
build in progress.  Nothing in this note should be read as a checked theorem
until that focused check has run.

The file contains no proof placeholder or new axiom.  Its public source-level
producers are:

- `edgeRicciHalf`, the exact Ricci half-combination left after adding and
  subtracting one Riemann coefficient;
- `edgeFold0`, the explicit lower residual after separating the DeTurck
  covariant-derivative arm from its endomorphism arm;
- `edgeZeroBoundAt` and `edgeMetric_bal`, which let the equal-radius public
  refold packages be used on the sharp-zero closed-edge path; and
- `edgeMvTrace`, which reconstructs through public APIs the exact identity
  between a moving-metric double trace and a fixed-background trace with one
  `fullRaisedEndoField` insertion;
- `edgePairMono` and `edgeMonoRefold`, which reconstruct the private
  pair-trace/Palatini monomial identity using the public `mvPairTraceOp` and
  `mvPairTraceOp_apply_toModel`;
- `edgeLiePairFam`, `edgeRiemPairFam`, and `edgeTopPair`, together with their
  exact action theorems, which package the full returned `C2` coefficient as a
  rank-two pair-trace field acting on `W`; and
- `edgeSlot2`, `edgeRaise2`, `edgeProd4`, and `edgePairPartner`, the explicit
  smooth rank-four formal-partner carrier for one moving monomial;
- `edgeSlot2_eval`, `edgeRaise2_eval`, `edgeProd4_eval`, and
  `edgePartner_eval`, which expose that carrier componentwise;
- `edgeMono_eval`, `edgePair_l2`, and `edgePair_inner`, which source-assemble
  the exact pointwise and global formal-adjoint identity for one public
  moving pair-trace monomial;
- `edgeLiePartner`, `edgeKernelPartner`, `edgeRiemPartner`, and
  `edgeTopPartner`, culminating in `edgeTop_inner`, the corresponding exact
  formal-partner identity for the complete top coefficient;
- `edgeTop_green`, which applies the closed-manifold covariant Green identity
  to that complete partner and moves the second derivative of `W` exactly onto
  `covDivergence edgeTopPartner`; and
- `exists_edgeRefold`, which directly consumes
  `exists_riemannPalatini_refold_identity_data` and
  `exists_deTurckLieCovDerivArm_refold_identity_data`;
- `exists_edgeSlopeRef`, which composes that producer with `edgeSlope_split`
  and exports the complete consumer-shaped `rhsSumSlope` normal form.

For every fixed smooth symmetric metric difference `W` with nonnegative
`delta <= 1/2`, `exists_edgeRefold` constructs its finite jet radius internally
and returns coefficient families `C0`, `C2` on the entire slope segment.  It
records all of the following in one producer:

1. the exact full tensor identity for `edgeQuadArm`;
2. a uniform pointwise bound for `C0`;
3. an explicit pointwise `O(delta)` bound for `C2`; and
4. the corresponding full Hilbert/L2 pairing identity.

No derivative bound on an arbitrary edge-path metric is an assumption of this
statement.  The internally chosen finite jet radius only instantiates exact
identities for the already smooth fixed tensor; it is not used as the final
closed-edge energy coefficient.

## Exact remaining energy producer

The refold deliberately leaves three structurally low-order terms visible:

- `edgeRicciHalf`, whose top connection derivative cancels in the Ricci
  half-combination;
- `edgeFold0`, consisting of the DeTurck endomorphism arm, `lieCorr0`, the
  curvature fold, and the fixed-carrier subtraction; and
- `edgeQuad1` acting on `nabla W`.

The next smallest mathematical producer is the joint closed-edge estimate

`<W, -2 edgeRicciHalf(W) + edgeFold0(W) + edgeQuad1(nabla W)
      + C2(nabla^2 W)>`

`<= c * delta * ||nabla W||_2^2 + K * ||W||_2^2`,

with `c * delta` small enough for the remaining principal absorption.  The
`C2` term must be integrated by parts in its Palatini/refold form; replacing it
by a standalone coefficient norm followed by a coarse H2 estimate would lose
the closed-edge argument.  Likewise, separately bounding `edgeRicciHalf` as a
generic order-zero coefficient would reintroduce an inadmissible dependence on
spatial derivatives of the arbitrary edge solution.

The pair-trace obstruction and its algebraic formal-adjoint step have now been
removed at source level without editing the claimed coefficient-refold file:
`edgeMonoRefold` is the public reconstruction, `edgePair_l2` moves one monomial
onto its rank-four partner, and `edgeTop_inner` reaches the complete `C2`
returned by `exists_edgeRefold`.  These declarations still await focused Lean
checking.

The covariant Green step is now present at source level as `edgeTop_green`; it
turns

`<W, appCc C2 (nabla^2 W)>`

into the first-order pairing of `nabla W` against the divergence of
`edgeTopPartner`.  The exact movement of both relative inverse-metric
insertions onto the two `W` factors is now represented by `edgePair_l2` and
`edgeTop_inner`.  Differentiating that explicit partner produces only products
containing one undifferentiated `W`, hence the required
`O(delta) * |nabla W|^2` bound.  This is materially different from estimating
`nabla C2` as a generic coefficient jet, which would destroy the sharp zero at
`W = 0` and introduce an inadmissible additive source.

Thus the exact remaining producer in this file is the structural divergence
bound for `edgeTopPartner`: pointwise, its squared fibre norm must be bounded
by a background constant times `delta^2` times the squared fibre norm of
`nabla W` (for `delta <= 1/2`).  The existing inverse-metric raised-endomorphism
jet grid and the operator-field diagonal product grid are the canonical APIs
for this step: order one of the former is linear in `nabla W`, while every
order-one product term retains one undifferentiated `W`, which supplies the
small `delta` factor.  A generic coefficient-jet envelope is not sharp enough.

## Progress accounting

- Exact endpoint `ricci_flow_forward_unique`: **0%** until that theorem is
  proved and checked.
- Closed-edge Ricci--DeTurck uniqueness machinery in this lane: source-level
  exact slope split, principal absorption, moving-energy bookkeeping, and full
  refold pairing are assembled; the joint low-edge estimate and its verified
  energy/Gronwall closure remain.
- `extends_of_rmBounded` and the Hamilton positive-Ricci endpoint are unchanged
  until both requested analytic producer theorems are genuinely proved.
