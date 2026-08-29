# ReducedLength

## Result

`redLength` is the standard normalization of fixed-time L-cost by
`2 * sqrt tau`.  The scalar lemmas `redLength_mul` and
`redLength_eq_zero` record the positive-time cancellation laws without making
any sign claim about L-cost or reduced length.

`redLength_diff_ae` proves that on a compact positive regular backward-time
slice, reduced length is manifold-differentiable outside a null set for any
smooth Riemannian volume measure.  It transports the checked chart-local
Lipschitz estimate for L-cost through one fixed nonzero scalar normalization
and applies the generic manifold Rademacher theorem.

`lCost_eq_branch` identifies fixed-time L-cost locally with the inverse-L-exp
action branch at every displayed strict minimizing tangent.  The proof pulls
the open `lInjDomain` back through the continuous local inverse.  Every nearby
inverse tangent still minimizes at a strictly later time, so
`lMinDomain_down` gives minimality at the displayed time; the local-inverse
identities and `lLength_sqrt` then identify its action with L-cost.

`lCost_hasMFD` transports the checked derivative of that smooth local branch
through the eventual equality.  Its only explicit geometric inputs are
positive backward time and strict minimizing membership; the positive
L-exponential domain and nonconjugacy are derived internally.  `lCost_grad`
then raises the resulting metric-flat cotangent and identifies the spatial
L-cost gradient with the terminal regularized-ray velocity.

`redLength_hasMFD` and `redLength_grad` apply the fixed scalar normalization
directly.  Thus the strict minimizing region now has a checked full manifold
differential and spatial gradient formula, not merely derivatives along test
curves.  `redLength_grad_ray` combines this with `lExp_vel_sqrt` and gives the
textbook form: the spatial reduced-length gradient is the ordinary
backward-time velocity of the minimizing L-exponential ray.

`lCost_hasDeriv` treats backward time with the endpoint held fixed.  It uses
the joint local diffeomorphism `(W,r) |-> (lExp W r,r)`, pulls the fixed-
endpoint time line back through its local inverse, and differentiates the
joint ray action with `lRayAct_joint`.  The differential of the local inverse
forces the endpoint motion to cancel.  A fixed later minimizing time keeps the
whole inverse branch inside `lInjDomain`, so the local action is genuinely
equal to L-cost rather than merely an upper support.

`redLength_hasDeriv` differentiates the normalization by `2 * sqrt tau` and
proves the fixed-endpoint formula

```text
partial_tau l = (R - |X|^2)/2 - l/(2*tau).
```

Together with `redLength_grad_ray`, `redLength_HJ` gives the pointwise
Hamilton--Jacobi identity on the strict minimizing region.

`lCost_hess_le` is the first checked second-order endpoint comparison.  For
any tangent field that is `C⁸` on an open neighborhood of the displayed
compact minimizing-ray interval, vanishes at square-root time zero, and has
prescribed terminal value `V`,
it bounds the fixed-time L-cost Hessian in direction `V` by twice that field's
regularized L-index.  The proof takes the local-inverse Jacobi field with the
same terminal value, writes the supplied field as `J + Q`, globalizes the
curve and both fields without changing their germs on the compact interval,
and uses minimizing action to prove `I(Q,Q) >= 0`.  The Jacobi Green identity
gives `I(J,Q) = 0`, while `lActBranch_hess` and `lCost_eq_branch` identify the
cost Hessian with `2 * I(J,J)`.  The germ-controlled globalization keeps the
clamp range inside that supplied neighborhood, so the theorem does not demand
global smoothness from the totalized regularized curve outside its maximal
domain.  The public hypothesis remains `C⁸` only where the proof uses it;
no minimizing or nonconjugacy assumption is added for the caller beyond strict
minimizing-domain membership.

`redLength_hess_le` performs the exact positive scalar normalization.  It
bounds the spatial reduced-length Hessian by `I(W,W) / sqrt tau`, using the
canonical constant-scalar Hessian law `hessFun_smul`; it adds no hypotheses to
the L-cost comparison.

## Verification

Focused verification passes without warnings for the local branch equality,
the spatial and time derivatives of L-cost, both forms of the reduced-length
differential and gradient, the reduced-length time derivative, and the
Hamilton--Jacobi identity, `lCost_hess_le`, and `redLength_hess_le`, including
the open-neighborhood germ interface.  The source contains no placeholder
proof, new class, frontier assumption, or sign claim.

The exported module refresh and the public L-geometry umbrella check also
pass.  Axiom audits of `lCost_hasDeriv`, `redLength_hasDeriv`, and
`redLength_HJ` report only `propext`, classical choice, and quotient
soundness.

## Project status

This is an L6 reduced-length brick.  The strict-region spatial differential,
gradient, fixed-endpoint time derivative, Hamilton--Jacobi, and abstract
index-form Hessian comparison substages are complete (100%).  In particular,
both `lCost_hess_le` and its normalized `redLength_hess_le` consumer are
theorem-complete, not just supported by infrastructure.
The next L6 frontier is the adapted-field ODE and trace contraction producing
the explicit Morgan--Tian Laplacian inequality.  That explicit trace theorem
remains unstated and unproved (0%); its branch-Hessian and index-minimization
machinery is now complete.

The theorem `redVolume_anti` remains unstated and unproved at 0%.  Dedicated
compact ordinary-flow L-geometry machinery is about 99%; generic chart-local
Lipschitz, manifold Rademacher, parametric-integration, differential, gradient,
and local-inverse infrastructure reused here is complete for these interfaces.

## Strict-region local smoothness

`lCost_smooth` now combines the public `lActBranch_smooth` producer with
`lCost_eq_branch`, shrinking their neighborhood germs to one actual open
neighborhood of the strict-ray endpoint.  `redLength_smooth` applies the fixed
scalar normalization on the same neighborhood.  Both conclusions are local
`ContMDiffOn ∞` theorems derived from positive time and strict minimizing-domain
membership; neither assumes a supplied smooth set or global smoothness.

Focused verification passed without warnings.  This local-smoothness bridge is
100% and is ready for the native Hessian-trace-to-Laplacian consumer.  The
explicit reduced-length Laplacian bound remains a separate theorem and is not
counted complete here; `redVolume_anti` remains 0%.
