# Chart inverse Gram matrix bridge

## Goal

Expose the chart inverse Gram matrix as the intrinsic basis inverse metric used
by tensor norm and trace formulas, without requiring compactness, boundary
conditions, or a selected global frame.

## Status

`chartInvGram_inverse` is implemented by reading the two matrix inverse
identities entrywise in the actual `chartBasisFamily`. Focused verification
passed without warnings.

This is a reusable producer only: it adds no compactness, boundary, chart
constancy, or global-frame assumption.

The downstream Hessian norm proof ultimately reconstructs the older
`MetricInverseInBasis` predicate entrywise at its one legacy consumer. Passing
the whole `_gen` predicate across that boundary caused the same topology-diamond
`whnf` blow-up as earlier whole-Hom proofs, whereas the scalar matrix identities
are cheap.
