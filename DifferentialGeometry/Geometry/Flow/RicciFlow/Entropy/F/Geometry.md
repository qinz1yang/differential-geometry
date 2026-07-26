# F geometry

## 2026-07-16 weighted scalar Green bridge

Added `weighted_grad_zero`, the scalar identity saying that the weighted
Laplacian integrates to its gradient drift against `e^{-f} dmu`.  It is a thin
specialization of the existing weighted divergence theorem to `grad q`, with
all bundle data evaluated before integration.  Focused verification passed
without a new `sorry`.

This is supporting machinery for the weighted Bochner and Hessian-square
identities; it does not by itself prove a `W` or no-local-collapsing endpoint.
