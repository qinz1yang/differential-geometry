# DifferentiatedSecondBianchi

## Role

This module owns the static-metric differentiated second Bianchi identity for
canonical lowered Riemann.  It is the lowest reusable geometric step before the
Ricci-flow Hamilton base evolution contracts and commutes the resulting
`\nabla^2 Rm04` terms.

## Status

`canRmSecond_nabla` is focused-green, exact-green, and contains no `sorry`.  The proof
reindexes the two cyclic terms as smooth rank-five tensor fields, differentiates
their field equality, and uses naturality of total covariant differentiation
under slot reindexing.

The first focused pass exposed two local API issues, both now closed:

- `ContMDiffSection.ext` requested an otherwise unnecessary rank-five bundle
  instance; dependent-function extensionality is the weaker and natural route.
- simplifying the front-extended permutation directly at rank six was brittle;
  first proving the rank-five tail equality makes the derivative slot remain
  definitionally fixed.

## Project accounting

- `canRmSecond_nabla`: 100% implemented and focused-verified.
- Dedicated differentiated-Bianchi machinery for this brick: 100%.
- Static arbitrary-dimensional Hamilton identity: 100% implemented and
  focused-verified in `Hamilton.lean`; its exact artifact refresh is pending.
- Arbitrary-flow base evolution producer theorem: not yet stated and proved,
  0%.  Its dedicated static and time-variation machinery is about 75%.
- `CurvBoundInput.movingShi_open`: 0%; its analytic producer chain remains open.
- Whole HCG compactness endpoint: 0%; this isolated tensor identity does not
  alter endpoint-level accounting.
