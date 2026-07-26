# EntropyJensen

## 2026-07-16 probability Jensen layer

`withDensity_prob`, `int_log_le_moment`, and `entropy_le_moment` are checked
without warnings or a local `sorry`.  Together they turn the normalized
density `v ^ 2` into a probability measure, apply Jensen to `exp`, and return
the entropy-moment estimate on the original measure.  The proof obtains the
needed measurability from `Integrable (v ^ 2)`; it does not add an
`AEMeasurable v` consumer assumption.

These three measure-theoretic producers are **100%**.  They are inputs to the
closed-manifold log-Sobolev theorem, not a no-local-collapsing endpoint.

## 2026-07-17 support entropy bound

`entropy_supp_le` is now checked without warnings.  For a measurable,
nonnegative unit-mass density `w` on a finite measure space, it proves
`-∫ w log w ≤ log (μ U).toReal` whenever `support w ⊆ U`.  The proof
uses the probability measure `w dμ` and the positive reciprocal random
variable that equals `w⁻¹` off the zero set and `1` on it, then reuses
`int_log_le_moment` at exponent one.  Zero-density points are handled before
all logarithmic rewrites.

This is a reusable measure-theoretic producer, not a cutoff or noncollapsing
endpoint.  It supplies the logarithmic-volume term required by the next
cutoff W upper estimate.
