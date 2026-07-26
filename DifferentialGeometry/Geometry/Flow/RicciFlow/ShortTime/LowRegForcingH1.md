# Low-regularity Ricci--DeTurck forcing

## Verified results

- `rhs_raw_lip` now uses the intrinsic metric 2-jet and therefore depends only
  on the background-covariant tensor jet through order 2 (`range 3`).
- `rhs_h0_lip` packages this as a uniform spectral `H2 -> H0` Lipschitz bound.
- `rhs_cov_lip` and `rhs_h1_lip` remain valid at their previous H3 input
  regularity; their lower-order raw-component uses now explicitly embed the
  2-jet window into the 3-jet window.
- Focused verification passes without local warnings or sorries.

## Mathematical route

The zero-order part of the eventual remainder estimate is now at the correct
regularity. The remaining H1 derivative cannot use `rhs_h1_lip` directly,
because that estimate retains the fixed background connection-Laplacian
third-derivative term. The next proof must subtract that term exactly and split
the derivative into:

1. a top third-jet factor multiplied by the small principal-cometric deviation;
2. lower metric-difference jets through order 2, with constants allowed to
   depend on the uniform C3 `LowRegCoeff` package.

The high-order three-arm theorem is not a low-regularity substitute: its
coefficient bounds require `a >= 2 * dim + 10`. The exact three-arm identity
and the low-order coefficient bounds must be separated before it can serve the
`a = 1`, dimension-three solver.

## Failed route retained

A pointwise first-derivative bound on the principal coefficient from endpoint
H2 data is too strong in dimension three. The valid route is the H2 coefficient
product estimate, using L4 cross terms, together with exact principal
cancellation.

## Honest accounting

- `rhs_raw_lip` at H2 input: theorem 100%.
- `rhs_h0_lip`: theorem 100%.
- Unconditional mixed H3-to-H1 remainder theorem: not yet stated/proved, 0%.
  The 60% machinery estimate was this file's historical snapshot and is
  superseded by the 2026-07-18 route ruling in `LowRegRemainderH1.md`.
- Uniform low-regularity Ricci--DeTurck existence theorem: not yet stated/proved,
  0%.
- Whole-program HCG accounting is maintained in `HCGCompactness/PROJECT_MAP.md`;
  this local forcing note does not carry a second percentage snapshot.
