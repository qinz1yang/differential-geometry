# TailEndpoint

## Result

`lTailLine_smooth` supplies the local smoothness bridge from a jointly smooth
positive-start family to its affine velocity-line field, using the canonical
local variation-field API.

`exists_lTail_inj` starts from the canonical minimizing-domain predicate, a
uniform Riemann-curvature bound on the regular backward slab, and a positive
regularized start before the terminal square-root time. It constructs one
spanning actual-velocity family and proves that the terminal endpoint map has
injective manifold differential at the minimizing central velocity.

The proof turns a kernel direction into a suffix Jacobi field, computes its
nonzero initial covariant derivative, globalizes the curve-and-field pair on
the whole minimizing segment, constructs the negative left-relative broken
index direction, and contradicts `lIndex_sum_nonneg`. The global fixed-endpoint
minimality input is derived from `lMinVec_min_rm`, which turns the canonical
curvature bound into the action lower bound needed for the infimum comparison.

## Verification and progress

The private endpoint contradiction and the public wrapper are verified. The
former compact-only call has been replaced by the new
`lMinVec_min_rm` producer, using `lRegCosts_bdd_rm` and
`lRegCostC1_le_bdd`. Neither the bridge nor the public endpoint assumes
`CompactSpace`, completeness, or a caller-supplied `BddBelow` fact.
`IndexNode.lIndex_sum_nonneg` has separately been weakened to
`SigmaCompactSpace` and verified.

Focused verification passes without warnings, and the targeted `TailEndpoint`
module refresh passes. Endpoint differential injectivity and its dedicated
machinery are complete (100%). The Calabi local inverse, the all-point weak
barrier, and `exists_redLen_le` remain 0%. `redVolume_anti` remains complete
(100%); dedicated L-geometry is about 53%, and reused generic infrastructure is
complete (100%).
