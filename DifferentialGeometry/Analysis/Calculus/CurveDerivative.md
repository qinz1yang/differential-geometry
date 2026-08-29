# `CurveDerivative.lean`

## Added API

`hasDerivAt_diag0` is a generic scalar chain-rule adapter.  For a jointly
differentiable family `F(s,x)`, if the spatial slice `F(s,-)` vanishes near the
base point, it proves that the derivative of `F(r, alpha r)` equals the
derivative of the frozen-base curve `F(r, alpha s)`.  The statement uses only
the manifold differentiability needed by the product chain rule and does not
introduce a geometric or Ricci-flow assumption.

The proof decomposes the product-manifold derivative into its time and spatial
parts; the spatial part is zero by eventual equality.  This is reused by the
backward connection-variation layer instead of duplicating a coordinate
calculation there.

## Verification

Focused verification passed without warnings.  No failed route or remaining
blocker is attached to this helper.
