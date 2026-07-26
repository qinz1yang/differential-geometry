# DistanceTent

## 2026-07-16 Riemannian distance tent

`riemDistTent` is the real-valued `r / 4`-thickened indicator of the closed
`r / 2` ball for the extended distance of an explicitly supplied smooth
Riemannian metric.  The checked API proves:

- values lie in `[0, 1]`;
- the function is `1` on the closed `r / 2` ball;
- it vanishes from radius `3 * r / 4` onward, including on components at
  infinite extended distance;
- its support lies in the open `3 * r / 4` ball and its topological support
  lies in the open radius-`r` ball;
- its explicit-distance Lipschitz constant is exactly `4 / r`.

The first prototype used `ENNReal.truncateToReal` and directly proved that a
truncated radial extended distance is unit Lipschitz.  That route checked, but
was removed after finding Mathlib's stronger canonical
`thickenedIndicator` API.  The live implementation is only a Riemannian
explicit-metric adapter and does not maintain a parallel generic tent API.

Focused verification and the targeted module build passed.  The later
`weak_grad_of_lip`, `grad_norm_aesm`, and `memW1p_of_lip` producers now give
this tent an intrinsic weak gradient with the exact `4 / r` pointwise metric
bound.  Thus the geometric tent, support bookkeeping, and intrinsic W¹,²
entrance are complete.  The remaining cutoff frontier is quantitative smooth
approximation: convert a small chart-W¹ error into a small intrinsic gradient
error, then impose support with a smooth outer multiplier.
