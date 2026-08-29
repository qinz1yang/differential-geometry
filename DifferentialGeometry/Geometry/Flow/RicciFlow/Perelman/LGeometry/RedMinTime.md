# RedMinTime

## Role

This module packages the spatial minimum of reduced length and its
square-root-time action normalization on a complete bounded-curvature slab.
It is the time-regularity input used by the reduced-length fencing argument.

## Checked results

- `redMinVal` is the infimum of `redLength S T x y tau` over the endpoint.
- `redMinAct` is the corresponding regularized action value at square-root
  backward time.
- `exists_redMin_vec` realizes the spatial minimum by an actual minimizing
  L-ray and returns its endpoint and minimum comparison.
- `redMinAct_lip` proves a quantitative Lipschitz bound on every positive
  square-root-time interval inside the bounded-curvature slab.
- `redMinVal_cont` transfers that result through `tau = sqrt(tau)^2` and proves
  continuity of the spatial reduced-length minimum at every positive time.

The Lipschitz proof compares the heads of minimizing rays in both time
directions. It uses the noncompact ray-action adapter and the two-sided scalar
potential bound produced from the slab Riemann-curvature bound; no ambient
compactness or desired continuity hypothesis is added.

## Verification and position

Focused verification is warning-free green, and the named module artifact is
refreshed. The definitions and all listed theorems contain no `sorry` or
`admit`. This time-regularity stage is 100%; its downstream consumer
`exists_redLen_le` is proved separately in `RedLengthFence`.
