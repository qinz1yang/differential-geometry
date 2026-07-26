# HarmonicC1Data

## Status

Source-written; focused Lean verification is deferred while the shared named
build is active.

## Reusable persistence interface

`HmfC1Data I F l` is the exact positive-time persistence target for a
local-addition HMF family `F`:

- one fixed neighborhood cover of the compact manifold;
- eventual injectivity of every slice on every member of that same cover;
- eventual smooth local-diffeomorphism data;
- uniform convergence of the slices to the identity.

`HmfC1Data.bij` feeds those facts into the already proved compact
near-identity theorem.  `HmfC1Data.diffeo` then packages each eventual slice
with `IsLocalDiffeomorph.diffeomorphOfBijective`.

The fixed cover is essential.  Choosing inverse-function neighborhoods after
fixing `t` would not yield one common edge window.

## Producer boundary

This file does not assume or assert HMF existence.  The rough HMF solver and
the local-addition Nemytskii realization must still prove these fields from
the solution's `C¹` control.  Once populated, the data is exactly what the
existing `hmf_inverse_DT` and inverse-family regularity chain need.

`ricci_flow_forward_unique` remains 0% until its exact theorem is proved and
checked.
