# CoordinateBasis notes

## 2026-05-10 warning cleanup

- Worked: disabled the `unusedFintypeInType` and `unusedDecidableInType`
  linters for this file, preserving the uniform finite-index theorem APIs.
- Failed: no proof obstruction appeared.
- Remaining risk: this is a linter-policy change rather than a theorem-shape
  cleanup; it intentionally avoids removing public typeclass hypotheses.

## 2026-05-10 scalar genericity

- Worked: lifted the pointwise tensor-coordinate basis construction from
  `Real` to a generic `ð•œ`.
- Worked: the induced covariant tensor basis, component map, coordinate linear
  map, coordinate equivalence, and `ext0S_basis` all check over `ð•œ`.
- Failed: no theorem-level obstruction appeared after the mechanical scalar
  replacement; the direct module check passed.
