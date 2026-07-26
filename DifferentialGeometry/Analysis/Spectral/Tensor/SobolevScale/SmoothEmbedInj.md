# SmoothEmbedInj

## 2026-07-19

The generic smooth covariant-tensor spectral embedding is injective at every
real order.  The proof
uses exactly two existing canonical facts: spectral coordinates are the full
Hilbert eigenbasis representation of the `L2` image, and
`SmoothCcTensor.toL2` is injective on continuous smooth representatives.

This removes an artificial supercritical-regularity dependency from the
well-definedness step of the dimension-three low-regularity
Ricci--DeTurck `Dense.extend` construction.  It does not by itself prove a
nonlinear estimate or either analytic endpoint theorem.

Focused verification is pending while the shared long-path `.olean`
dependency is being rebuilt exclusively by the product-estimate lane.
