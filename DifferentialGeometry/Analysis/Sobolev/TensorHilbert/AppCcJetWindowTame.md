# AppCcJetWindowTame

## 2026-07-13 rank-generic coefficient-jet integration

`appCc_jet_l2Sq_le` is now the rank-generic bridge from pointwise coefficient
jet square bounds to an `L²` jet square estimate for `appCc`.  It keeps arbitrary
operator ranks `b`, `c` and an arbitrary input `W`; the right side is the
diagonal lower-jet window supplied by `appCcGdiag`.

The proof directly integrates
`appCc_iteratedCovGrad_diagonalProductGrid_le`.  It adds no spectral-family,
moving-metric, Sobolev-embedding, or finite-support assumption.  The first
check exposed only local syntax and integral-congruence elaboration issues;
after replacing generic congruence with typed finite-sum congruences,
verification passed.

Honest scope: this producer theorem is complete (100%).  The target theorem
`scalar_crit_tame` remains unstated and unproved (0%); this helper is only a
small part of its dedicated machinery (about 5%).  Coefficient realization,
uniform coefficient-jet bounds, and conversion of the resulting covariant-jet
estimate to the scalar spectral Sobolev norm remain separate frontiers.  The
Perelman no-local-collapsing endpoint and `ham3_noncollapse` remain 0%.
