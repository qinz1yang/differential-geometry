# Left-relative negative index algebra

## Result

`exists_lSplit_left` is the algebraic mirror of `exists_lSplit_neg`.  A
zero-index suffix direction with negative cross index against a global test
field gives, after a suitable positive scaling, a pair of matching broken
directions with strictly negative total regularized L-index.

`lIndex_cross_neg` is the corresponding Green-identity sign producer.  If a
suffix Jacobi field has nonzero covariant derivative at its positive left
endpoint, a test field equal there to the positive scalar
`c * (b - c)` times that derivative and vanishing at `b` has strictly negative
cross index on `[c,b]`.

## Role

For a positive-start suffix Jacobi field vanishing at both `s0` and `b`, the
Green identity makes the cross index negative when the test field at `s0`
points along the initial covariant derivative.  This theorem then produces the
negative pair that contradicts `lIndex_sum_nonneg` for the original globally
minimizing ray.

The remaining geometric assembly must supply a globally smooth representative
of the suffix field, show its initial covariant derivative is nonzero, choose
the test field, establish the integrability hypotheses, and apply the
minimizing index inequality.  No endpoint differential injectivity theorem is
claimed here.

## Verification

Focused verification passes without warnings or placeholders, and the named
module artifact has been refreshed.  The left-relative algebraic split and its
Green cross-index sign are complete (100% each).  Endpoint injectivity and the
Calabi local inverse remain 0% until their declarations are proved.

In whole-plan accounting, `redVolume_anti` remains complete (100%), dedicated
L-geometry including the open barrier and existence endpoints is about 48%,
and reused generic infrastructure is complete (100%).
