# `AdaptedTrace.lean`

## Result

`lIndex_trace` is proved (100%).  It sums `lIndex_adapted` over a
finrank-sized family of adapted fields whose terminal values are orthonormal
for the terminal metric.  Constancy of the moving metric pairing propagates
orthonormality to every point of the square-root interval.  The native
orthonormal Ricci trace and metric-scalar bridge then contract the finite Ricci
sum to `S.scalar`; the terminal norm sum contracts to the real dimension.

The result is an exact finite-sum equality.  It retains the honest summed
regularized index density under the interval integral and introduces no
Hamilton `H`, time-Ricci, or desired-conclusion assumption.  This is the form
directly consumed after the scalar Hessian trace of `redLength_hess_le` in the
Morgan--Tian Laplacian comparison.

`lIndex_trace_pos` is proved (100%) for every `a < b`.  It uses the
positive-start endpoint fields
`W_i(s) = ((s - a) / (b - a)) P_i(s)`, hence contributes the boundary trace
`finrank / (2 * (b - a))`.  The remaining integral has weights
`((s - a) / (b - a)) ^ 2` on the regularized index density and
`2 * s * (s - a) / (b - a) ^ 2` on scalar curvature.  The proof consumes
`lIndex_smul_pt` directly and adds no affine wrapper or positivity assumption
on `a`.

## Verification and project status

Both the original zero-start theorem and the positive-start theorem passed
focused verification without warnings or placeholders.  The only local repair
for `lIndex_trace_pos` was removing a redundant `ring` after `field_simp` had
already closed the scalar identity.  Its named artifact is intentionally not
refreshed until a downstream module actually consumes the new export.  The
explicit positive-start Morgan--Tian Laplacian inequality is not yet stated or
proved (0%).

`redVolume_anti` remains a checked 100% endpoint, but the all-point spacetime
weak barrier, `exists_redLen_le`, `redVolume_late_low`, `smooth_nlc`, P2, and
the final Poincare endpoint remain 0%.  Dedicated L-geometry across the open
L8--L9 lane is about 55--57%; reused generic infrastructure is 100%; the whole
P0--P9 infrastructure estimate remains 15--25%.
