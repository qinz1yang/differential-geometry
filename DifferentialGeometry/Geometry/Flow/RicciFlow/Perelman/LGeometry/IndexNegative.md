# IndexNegative

## Verified producers

- `exists_lTest` extends a prescribed tangent vector to a globally smooth
  polynomial test field along a globally smooth curve.  It vanishes at the two
  chosen endpoint times and has the required scaled value at the interior
  node.
- `lRegJacobi_d_ne` proves that a nonzero canonical regularized L-Jacobi field
  with a positive-time zero has nonzero moving covariant derivative there.
  The proof uses the native first-order uniqueness theorem and the normalized
  initial derivative `lRegJacobi_d0`.
- `lIndex_cross_pos` is the Green-formula consequence needed by the broken
  field argument: a test field pointing in the nonzero terminal derivative
  direction has strictly positive cross index on the conjugate prefix.
- `exists_lSplit_neg` carries the honest `JJ`, `JW`, and `WW` integrability
  hypotheses required by the interval-integral quadratic expansion.  It picks
  a scalar for which the two branch indices have negative sum.
- `lIndex_neg_conj` globalizes the regularized ray and canonical Jacobi field,
  transfers the Green identities through curve/field germs, constructs the
  polynomial test field, and returns two globally `C8` directions.  They
  vanish at the outer endpoints, match at the conjugate node, and have
  strictly negative total branch index.

Focused verification passes without warnings or placeholders.

## Route and frontier

The fixed-Hilbert reduction is intentionally not used: the moving metric would
require an unbuilt Uhlenbeck-frame realization and an exact comparison with the
intrinsic L-index.  The native route instead combines the positive cross term
with two smooth branch fields meeting at the conjugate node.  A common-flow
pair realizes both branches as variations; fixed-endpoint minimality then makes
the sum of their second variations nonnegative, contradicting the elementary
negative quadratic expansion.

The native statement is branchwise rather than a falsely fixed-node single
variation.  Moving the common node is exactly what preserves the positive
Green cross term.  `IndexNode.lIndex_sum_nonneg` supplies the matching
minimality inequality for those two branches.

`lIndex_neg_conj` is now complete.  The next exact endpoint is
`lMinVec_nconj_lt`, obtained by combining it with `lMinVec_reg_min` and
`lIndex_sum_nonneg`.  `redVolume_anti` remains 0%; the completed producer is
dedicated L-geometry machinery and does not count toward that capstone.
