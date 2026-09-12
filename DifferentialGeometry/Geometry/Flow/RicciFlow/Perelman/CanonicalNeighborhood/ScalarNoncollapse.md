# Strong scalar and spatial noncollapsing

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
Claim: 8c5ff5d8-d45c-4949-9791-6ce902b5c969 (shared three-file batch).
2026-09-08 20:09 UTC: VERIFIED, five public theorems.

Combine the scalar-only cutoff estimate with a uniform lower W bound and the
early-slab volume theorem. Preserve the native strong-scalar predicate: the
conclusion is required for every smaller concentric ball. The analytic volume
argument is dimension-independent; the currently available w_span_uniform
producer requires dimension 3, so distinguish the general conditional entropy
consumer from its fully instantiated three-dimensional endpoint. This is
Chapter25 proof work; do not implement missing earlier entropy inputs here.

Endpoints: `strongScalarNoLocalCollapsing_of_lowerW`,
`strongScalarNoLocalCollapsing_three`, `spatialNoLocalCollapsing_three`,
in `DifferentialGeometry.PDE.RicciFlow.Perelman`.
Final focused check: 25.6s EMPTY, after removing unused section assumptions.
Named build: 27s, lint-clean. Joint external audit: 28.4s, all five declarations
standard-only, including the actual instantiated 3D endpoints. Receipt:
`E:/lean-tools/chapter25-audit-20260908/noncollapse-completion.json`.
Every smaller concentric ball and the initial slice are included. Root import
is unique; the shared batch claim is released after registration.
