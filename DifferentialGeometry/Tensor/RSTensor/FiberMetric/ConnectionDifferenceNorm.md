# Connection-difference contraction norm

## 2026-07-10

Added `connOut_norm_le`, the scalar-applied specialization of
`sqrt_normSqRS_apply` to `connectionDifferenceTensorAt`.  The proof uses a
cheap scalar `change`; it never asserts equality of whole Hom objects.

Focused verification passed.  This producer is complete; downstream still
has to combine it with the metric C1 modulus and the Hessian/gradient spectral
energy bounds in the geometric `A2` estimate.
