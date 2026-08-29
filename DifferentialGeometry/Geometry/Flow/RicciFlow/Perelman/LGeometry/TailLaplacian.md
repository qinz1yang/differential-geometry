# TailLaplacian

## Scope

This module traces the positive-start tail Hessian comparison over a supplied
terminal-orthonormal family.  It stays at the fixed-time tail-branch layer and
does not assume an adapted-field ODE or any index-density integrability.

## Verified state

`lTail_lap_le` is warning-free focused GREEN.  Its full-span
minimizing-family hypotheses
match `lTail_hess_le`.  For each terminal field `P i`, it uses the scaled
comparison field

`W_i(s) = ((s - a) / (b - a)) • P_i(s)`.

The proof obtains local smoothness of the actual tail-action branch from
`lTailBranch_smooth`, identifies its Laplacian with the metric trace of its
Hessian, realizes the supplied terminal-orthonormal family as a basis, applies
`lTail_hess_le` in every basis direction, and sums the inequalities.

The focused verification consumed the explicitly refreshed `TailHessian`
artifact.  No named refresh was run for this module because no downstream
module yet consumes its new export.

## Progress accounting

- `lTail_lap_le`: **100% theorem endpoint**.
- dedicated positive-start tail Laplacian machinery through the raw traced
  index bound: **100%**.
- the later Hamilton substitution `lTail_lap_K`: **0%**.
- the all-point spacetime weak-barrier endpoint: **0%**.

The next exact theorem is `HamiltonBound.lTail_lap_K`, which should substitute
the already checked positive-start Hamilton trace identity into this raw traced
index bound.  It must not add adapted-ODE or integrability assumptions already
discharged by the existing trace producers.
