# SmallReduced

## Purpose

`lRedJac_zero_lim` is the intrinsic pointwise small-time normalization of the
pulled-back reduced Jacobian.  A single later strict-minimizing witness supplies
the displayed strict domain at every sufficiently small positive squared time.

`lRedJac_le_gauss` combines this right-hand limit with the checked ray
antitonicity theorem.  At a positive displayed time in the strict minimizing
domain, antitonicity bounds the reduced Jacobian by all sufficiently small
positive squared-time values; `ge_of_tendsto` passes that bound directly to the
zero-time Gaussian limit.

`lRedJac_tau_lim` is the corresponding theorem in the original backward-time
parameter.  It composes `lRedJac_zero_lim` with the positive right-neighborhood
map `tau ↦ sqrt tau` and uses `(sqrt tau)^2 = tau` for positive `tau`; it adds no
domain or endpoint-exhaustion assumption.

The proof combines the normalized L-exponential density limit with the
reduced-length limit.  At positive square-root time, the two logarithmic scale
terms in `redDensity` are evaluated exactly as `(2s)^n` and
`pi^(n/2)`.  The fixed positive source density is then cancelled only after the
model-coordinate product limit has been obtained.

## Verification

Focused verification of `lRedJac_zero_lim`, `lRedJac_tau_lim`, and
`lRedJac_le_gauss` passes without warnings or proof placeholders, and the
targeted module refresh is green.  The two affected `RayEndpoint` callers now
explicitly downgrade their existing order-two regularity proofs to the weaker
order-one parameter-integral interface; no public statement changed.  No new
geometric assumption, foundational class, or source-coordinate quadratic-form
wrapper is introduced here.

## Project position

`lRedJac_le_gauss` is the pointwise Gaussian upper bound on the strict domain.
It does not prove the full reduced-volume limit: that separate theorem still
needs eventual exhaustion of the strict minimizing domain for every source
tangent vector.
