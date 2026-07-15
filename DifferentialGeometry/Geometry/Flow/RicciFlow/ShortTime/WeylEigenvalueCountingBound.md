# WeylEigenvalueCountingBound

## 2026-07-14 live audit

The theorem `weyl_pointwise_diagonalKernel_bound_of_closed` is not proved
(theorem completion 0%). Its single `sorry` packages two different claims:

- a polynomial pointwise diagonal-kernel bound for arbitrary tensor valence;
- point-evaluation summability and eigen-expansion for `(0,2)` tensors at every
  order satisfying `2 * a > dim + 4`.

The proved Mercer machinery currently supplies a non-sharp pointwise estimate
only for `(0,2)` tensors. The generic-valence first conjunct therefore has no
current producer. The non-sharp estimate also does not by itself imply the
stated low threshold in the second conjunct.

The actual interior-smoothing consumer needs only `(0,2)` eigenvalue-tail
summability. It has been rewired to the proved
`tensorEigen_summable_negpow` producer, with verification pending.

For the realize-functional consumer, the fixed short-time order
`a = 4 * dim + 10` is much larger than the public statement's threshold. At
that order, a concrete proof route uses `abs_eigenBilinScalar_le`, negative
Sobolev-weight summability, and `tensorHs.weightedProd_summable`; a probe is in
progress. This would remove the deferred local-Weyl input from the actual
high-order short-time route, but it would not prove the stronger theorem as
currently stated.

Verification of the consumer rewiring and high-order probe is currently blocked
only by the active rebuild of a missing upstream Spectral object file.
