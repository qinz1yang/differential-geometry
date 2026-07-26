# DyadicScale

## 2026-07-17

Added the scalar first-crossing selector `exists_ratio_cross` and its dyadic
specialization `exists_dyadic_scale`.  The latter formalizes the exact scale
selection used in Perelman's cutoff argument: once normalized volume begins
below a fixed threshold but eventually crosses it at half-scales, the scale
immediately before the first crossing has outer/half-scale volume ratio less
than `2^n`.

This is genuine selector mathematics, not the missing geometric input.  The
remaining producer is a pointwise small-geodesic-ball Euclidean density lower
limit, sufficient to show that the dyadic normalized volumes eventually cross
one universal threshold.

Also added `exists_drop_lower`, the form used by the final geometric route.
A nonnegative normalized-volume sequence with a positive eventual lower bound
cannot decay by one fixed factor forever; at the first failure of geometric
decay its value is still no larger than the initial value.  This removes any
need for a uniform small-ball density constant.

Focused verification passed without warnings.
