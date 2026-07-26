# LineSplit.lean

## Purpose

This module owns the pure codimension-one metric-trace decomposition used by
the fixed-first radial Laplacian route.  It belongs below comparison geometry:
the statement uses only a pointwise Riemannian metric, a distinguished nonzero
line, a maximal independent perpendicular family, and a covariant two-tensor.

## 2026-07-23 status

- `trace_eq_line_add` is focused-green and contains no placeholder.  It is
  proved without assuming that the two-tensor is symmetric; the focused check
  is also linter-clean without file-global warning suppressions.
- The proof forms the adapted `Option ι` basis (`none ↦ Z`,
  `some i ↦ V i`), reads the inverse metric in that basis, and identifies its
  coefficients as the radial reciprocal, zero mixed blocks, and the inverse
  transverse Gram matrix.  The last identification uses the transverse block
  as a left inverse of the Gram matrix.
- The theorem itself and this pure trace-splitting layer are 100%.  The
  downstream `radialLap_eq_mean` theorem remains 0%; its dedicated fixed-first
  radial machinery is approximately 40% after this algebraic layer and the
  separately checked inverse-branch work.  The whole HCG supporting machinery
  remains approximately 60%, while the unconditional `compactnessSol` theorem
  remains 0%.
