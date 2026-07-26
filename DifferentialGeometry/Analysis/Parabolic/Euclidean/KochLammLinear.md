# KochLammLinear

## Purpose

This file proves the exact principal-flux estimate for the Koch--Lamm
carrier.  A coefficient family with operator norm at most `eps` multiplies
both the local `L²` and late `L^(n+4)` radii by `eps`.

This is the correct critical smallness mechanism for the local-addition
harmonic-map heat flow.  No horizon gain and no pointwise gradient arm is
inserted.

## Proved source content

- `eLpNorm_clm_le`: uniform continuous-linear-map bounds act on arbitrary
  `eLpNorm` spaces.
- `kl1_map_bound`: the corresponding endomorphism of `KLSource1`.
- `klPath_map_bound`: the gradient field of a `KLPath` gives the same
  controlled principal flux.

## Verification state

Focused verification passes with no local warning.  The remaining nonlinear
producer is the quadratic-gradient map into both arms of `KLSource0`; the full
heat map and `ricci_flow_forward_unique` endpoint remain unproved, so the
endpoint is 0%.
