# JacobiGram.lean

## 2026-07-17 Gram determinant calculus

Added the reusable curve-level objects `curveGram`, `curveGramDeriv`,
`curveMixedGram`, and `curveDensity`.  For a finite field family, the module
now proves Hermitian symmetry, the quadratic-form identity, positive
definiteness from fibrewise linear independence, positivity of the determinant
and density, and derivative formulas for the Gram matrix and its square-root
determinant density.

When the mixed Gram matrix is symmetric, `gramDeriv_eq_two` and
`hasDerivAt_symmDen` expose the factor-two form used by radial Jacobi/Riccati
arguments.  Focused verification and the explicitly named module build passed
without new warnings.

This is determinant calculus only.  On the selected normal-coordinate source,
linear independence should be a short consequence of the invertible
`expMapDiffeo` differential after the radial time-scaling bridge.  The
substantial Bishop--Gromov producer still missing is the shape-operator trace
Riccati inequality derived from the Ricci lower bound.
