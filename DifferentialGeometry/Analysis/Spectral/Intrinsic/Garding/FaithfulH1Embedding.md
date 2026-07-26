# Faithful H1 embedding

## Status (2026-07-10)

The covariant-rank eigenvector realization is now exposed by
`smoothEigen_h1_eq` for every `(0,s)` rank.  The associated per-step spectral
identity is likewise exposed by `oneMinus_coeff` at every covariant rank.  The
algebraic consequence `rawLap_coeff` now gives the corresponding rough-
Laplacian coefficient identity at every covariant rank.  These results use the
existing unconditional `loweringIntertwiner_gen` producer and introduce no
consumer assumptions.

The previous `(0,2)` theorem remains as a compatibility wrapper around the
general result.  Focused verification passed; the only reported linter warning
was pre-existing and belongs to a later theorem.

This closes the general coefficient-level spectral bridge needed by the scalar
connection-Laplacian lane.  The next target is its `s = 0` finite-support
representative packaging.

## Project position

- `smoothEigen_h1_eq`: 100% checked;
- `oneMinus_coeff`: 100% checked;
- `rawLap_coeff`: 100% checked;
- rank-zero spectral/actual Laplacian bridge: roughly 45% machinery, endpoint
  theorem 0%;
- moving-metric `A2`: theorem 0%;
- Perelman no-local-collapsing: theorem 0%, with dedicated machinery roughly
  20%;
- whole HCG compactness machinery: roughly 45%, endpoint theorems 0%.
