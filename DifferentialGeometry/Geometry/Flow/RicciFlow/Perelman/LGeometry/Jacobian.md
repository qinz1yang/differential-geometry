# Jacobian

## Purpose

This module provides the finite Gram-matrix and determinant calculus for a
family of tangent fields measured by the backward Ricci-flow metric.  It is
the scalar layer needed before specializing to the differential of `lExp`.

## Status

The generic Gram and determinant derivatives and their L-exponential
specializations are checked.  The moving metric contributes the explicit
`+2 Ric` term, while positivity comes from linear independence through the
native fixed-time Gram determinant theorem.

`lExpTrace_eq` identifies the logarithmic determinant trace with the spatial
reduced-length Laplacian plus scalar curvature.  `lExpJac_hasDeriv`,
`lExpLog_hasDeriv`, and `lExpLog_deriv_le` provide the intrinsic Jacobian rate
used by the canonical monotonicity theorem.  Focused verification passes
without warnings or proof placeholders.
