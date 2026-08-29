# JacobiSmooth

## Result

`lRegJacobi_smooth` proves that the total-space section formed by
`lRegJacobiField` is jointly smooth in the initial tangent vector and
square-root time on `lRegJointDom`.

The proof reuses `lRegCurve_smoothOn`, differentiates its joint tangent map in
the source direction `(V, 0)`, and identifies that derivative with the
fixed-time initial-tangent derivative defining `lRegJacobiField`.

## API choice

The theorem is joint in `(Z, s)`, rather than only smooth along one fixed ray,
so later compact localization and parameter variation can reuse it directly.
It introduces no new smoothness assumptions.

The product source uses the canonical equivalence between the tangent bundle
of `E × Real` and the product of the two tangent bundles. Directly rewriting
the product model as a self model failed because the charted-space instance is
dependent; the canonical tangent-product equivalence is the stable route.

## Verification

Focused verification passed without warnings. There are no `sorry` or
`admit` terms.

## Next frontier

Use joint smoothness to globalize the canonical Jacobi field on a compact
regularized ray, then prove that an interior zero of a nonzero canonical
Jacobi field has nonzero moving covariant derivative. This feeds the
L-specific negative broken-field construction for `lIndex_neg_conj`.
