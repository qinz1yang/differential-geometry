# ChartTimeC1

## Purpose

This module supplies the fixed-chart `C¹` recovery adapter for manifold curves
represented by `timeH1` paths.

## API route

- `curve_c1_local` reconstructs the shifted curve through
  `extChartAt.symm ∘ u.toFun`.
- The inverse chart is composed with the assumed `ContDiffOn ℝ 1` regularity
  of `u.toFun` on the normalized interval.
- The representative identity and the left inverse of `extChartAt` identify
  this reconstruction with `r ↦ alpha (a + r)`.
- Composition with the translation `s ↦ s - a` returns the result to
  `[a, b]`.
- No ordering hypothesis on `a` and `b` is needed: in the intended case
  `a ≤ b` this is the usual compact interval statement, while for `b < a`
  the domain and conclusion are both empty. This keeps the reusable adapter at
  its weakest assumptions.

## Verification

Focused verification passed without warnings. The module contains no
`sorry`/`admit`, and its sole public declaration satisfies the project naming
limit.
