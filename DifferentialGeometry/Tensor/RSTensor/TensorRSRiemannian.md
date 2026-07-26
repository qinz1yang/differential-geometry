# Mixed-tensor Riemannian norm

## 2026-07-10

Added `sqrt_normSqRS_apply`, the fiberwise Hilbert--Schmidt estimate
`|A input| <= |A| |input|` for the realized Hom model.  The proof selects only
a pointwise metric-orthonormal basis, expands all three intrinsic squared norms
into finite component sums, and applies finite Cauchy--Schwarz.  It does not
construct a frame or compare dependent fibers.

Focused verification and the targeted module build passed.  This producer is
complete; the geometric `A2` theorem remains unstated and unproved.
