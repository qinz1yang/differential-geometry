# LocalBranch

## Verified content

Focused verification passes without diagnostics.

- `upper_deriv_eq` and `not_diff_two_upper` give the generic upper-touching
  barrier calculus.
- `lActBranch` lifts an endpoint through the native fixed-time local inverse of
  `lExp` and evaluates the canonical regularized ray action.
- `lActBranch_cont`, `lActBranch_upper`, and `lActBranch_touch` establish the
  center continuity, eventual L-cost upper bound, and equality at a minimizing
  center ray.
- `lActBranch_hasMFD` gives the full manifold Frechet derivative of the local
  action branch at its center: the terminal ray velocity lowered by the
  terminal metric.
- The private local producers `lRayAct_smooth` and `lActBranch_grad_on`, together
  with the public `lActBranch_smooth`, establish an infinity-order action germ,
  its pullback through the local inverse, and the terminal-velocity formula for
  its gradient throughout a smaller open neighborhood.
- `lActBranch_hess` identifies the Hessian at the branch center with the
  terminal metric pairing against the covariant derivative of the regularized
  L-Jacobi field induced by the differential of the local inverse.
- `exists_branch_deriv` constructs a common smooth local regularized-ray family
  and a global time clamp, then proves the endpoint first-variation formula for
  the branch along every global smooth endpoint curve contained in a suitable
  neighborhood.
- `lCost_nondiff_two` uses one bounded endpoint curve with velocity equal to the
  difference of the two terminal ray velocities.  The two upper branches then
  have different derivatives by metric positivity, so the fixed-time L-cost is
  not manifold-differentiable at the common endpoint.

## Native APIs reused

The proof uses `lExp_localDiffeo`, `lRayAct_hasFDeriv`,
`mfderivToContinuousLinearEquiv`, `lRayLag_smooth`, `lRegFamily_extend`,
`lRegCurve_eqOn`, `lRegAction_bdry`, `lRay_end_vel_ne`, `lCost_le_ray`,
`exists_smooth_curve`, `hessFun_eq_cov_local`, and
`commute_ds_dt_intrinsic`.  The full derivative producer composes the initial-ray
action derivative with the local inverse and cancels `dExp` after `dInv`
through the native continuous-linear equivalence.  The smooth time clamp is
kept inside the common family domain.  No whole bundle map, Hom representation,
or reference-tree object is unfolded or compared.

## Route assessment

The parameter-dependent action differentiability layer is now supplied by
`lRayAct_hasFDeriv`, so the full branch derivative is a short local-inverse
chain-rule proof.  The older one-dimensional branch route remains useful for
the checked two-upper-barrier argument.

### Hessian route

The Hessian route is now complete.  A radial parameter clamp and the existing
time clamp globalize the local ray family without changing its center germ.
`lRayLag_smooth` and `contDiffOn_paramIntervalIntegral` then produce an
infinity-order fixed-time action germ.  Pulling that germ through
`lExp_localDiffeo.localInverse` gives the local smooth branch and makes its
terminal-velocity gradient differentiable.

For the second variation, a bounded endpoint curve realizes the prescribed
endpoint tangent.  The canonical smooth family from `lRegFamily_extend`
realizes its lifted initial tangent; `commute_ds_dt_intrinsic` exchanges the
two covariant derivatives, and `covDerivAlong_congr_curve` identifies the
result with the regularized L-Jacobi field.  The strengthened C-infinity
conclusion of `exists_smooth_curve` in `BoundedCurve.lean` removes the prior
artificial order-eight mismatch.  Finally `hessFun_eq_cov_local` converts this
gradient derivative into the public Hessian identity.

## Progress accounting

- `lCost_nondiff_two`: proved and verified, 100%.
- Full local action-branch manifold derivative: proved and verified, 100%.
- `lActBranch_hess`: proved and focused-verified, 100%.
- Dedicated local action smooth-germ, gradient-germ, and L-Jacobi Hessian
  machinery for this theorem: 100%.
- Dedicated multiple-minimizer geometric machinery needed by
  `lCutMulti_null`: approximately 100%; final cut-locus assembly and measure
  conversion remain separate tasks.
- `lCutMulti_null` itself: 0% in this file; it is not stated here and must not be
  counted complete until its assembly module verifies.
- Generic reused smooth-variation, parametric-integration, local-inverse,
  Hessian, and covariant-chain-rule infrastructure: complete for this producer,
  but counted separately from the target theorem.
- `redVolume_anti`: 0%.

## Public smoothness producer

`lActBranch_smooth` is now public with its existing weakest-assumption
signature.  It returns an open neighborhood of the center endpoint on which
the inverse-L-exp action branch is `C∞`; no proof or mathematical hypothesis
changed.  Focused verification and the exported-module refresh both passed.
