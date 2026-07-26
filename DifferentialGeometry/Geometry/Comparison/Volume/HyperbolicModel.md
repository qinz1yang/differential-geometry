# HyperbolicModel.lean

## 2026-07-17 V2 scalar model

Added the nonpositive-curvature warping function `hypSn`, its radial derivative,
the transverse area density `hypDensity`, and checked derivative and positivity
theorems.  Added `hypRatio_anti`, which turns the Bishop cross-derivative
inequality into antitonicity of the radial Jacobian/model-density ratio.

This is scalar V2b machinery.  The geometric Riccati/index-form inequality
supplying `hcross` remains unproved, and Bishop--Gromov itself remains 0%.

Added `hypSn_continuous`, `hypDen_continuous`, and
`hypVolumeRatio_anti`.  The last theorem composes the pointwise density-ratio
comparison with `integralRatio_anti`, so a radial Jacobian satisfying the
Bishop cross-derivative inequality now yields the cumulative radial-volume
ratio monotonicity directly.

Focused verification and the explicitly named module build passed.  This
completes the scalar model endgame only.  The next mathematical producer is the
cross-derivative inequality for the manifold radial Jacobian along a
no-conjugate radial geodesic; polar integration and cut-locus transfer remain
separate later frontiers.

Added the model Jacobi ODE `hasDerivAt_hypSnD`, the conserved energy identity
`hypSn_energy`, the logarithmic model density derivative `hypMeanCurv`, its
scalar Riccati equation `hasDerivAt_hypMean`, and
`hypDenDeriv_eq_mean`.  These identify the exact scalar comparison term that
the manifold trace-Riccati theorem must dominate.  Focused verification and the
explicitly named module build passed.

## 2026-07-23 mean-curvature growth bound

Added the public scalar estimate `hypMeanCurv_le`:

```text
hypMeanCurv q d r <= (d : Real) / r + (d : Real) * q
```

for `0 <= q` and `0 < r`.  The proof handles the Euclidean `q = 0` case
directly.  For positive `q`, it combines `x <= sinh x` with
`cosh x - sinh x = exp (-x) <= 1`, then divides only by explicitly positive
quantities.  This is the quantitative model term needed by the Route B-prime
distance-barrier estimate; it does not prove the geometric Laplacian comparison
or the complete Bernstein endpoint.

Focused verification passed without diagnostics, and the exact targeted
refresh is GREEN (`2615/2615`).  The theorem itself is complete; the larger
Route B-prime cutoff producer and unconditional complete-Shi theorem remain
open.
