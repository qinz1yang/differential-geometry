# CollapseScale

## 2026-07-17

Added the genuine geometric restriction operation `FlowMetricBall.shrink`.
The checked target is that factors in `(0,1]` preserve all-time ball inclusion,
distinguished-time nesting, and the full backward-parabolic
`IsRmControlled` predicate.  This is the transfer needed to apply the W cutoff
at the dyadic scale chosen by `exists_dyadic_scale`.

The file now also contains the concrete selector `exists_coll_scale`.
Normal-coordinate density positivity supplies an eventual pointwise lower
bound for normalized volumes, while `exists_drop_lower` supplies the first
dyadic scale where geometric decay fails.  The selected genuine flow ball is
nested in the original, inherits the full backward parabolic curvature bound,
has no larger normalized volume, and obeys the exact outer/half-ball doubling
inequality consumed by the cutoff W estimate.  No Bishop--Gromov or uniform
injectivity-radius input is required.

Focused verification passed without warnings.
