# IntrinsicEmbedding

## 2026-07-16 uniform intrinsic estimate

`sobolev_intrinsic` is checked.  It composes the constant-first chart theorem
`sobolev_closed` with the existing uniform reverse chart-to-intrinsic component
bound.  The resulting single constant controls the sub-critical `L^{p*}` norm
of every smooth scalar by its intrinsic `L^p` norm plus the `L^p` norm of its
Riemannian gradient.

Focused verification passed without warnings or a new `sorry`.  The uniform
intrinsic Sobolev producer is **100%**.  It is a real input to the entropy
estimate, but the entropy Jensen/log-Sobolev theorem and `w_fixed_lower` remain
theorem-level **0%**.

## 2026-07-16 `L²`-based specialization

`sobolev_lpNorm` is checked.  It specializes the intrinsic estimate to the
`lpNorm` normal form consumed by `logSobolev_closed`, with one constant chosen
before the smooth scalar.  This producer is **100%**.  The downstream Jensen,
log-Sobolev, and fixed-metric W lower-bound layers are now also checked; the
remaining genuine analytic frontier is the quantitative intrinsic ball cutoff.
