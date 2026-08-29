# Compact-slab constants for the min--max estimate

## Result

`lGrad_bound` gives a nonnegative constant on every compact interval of
regular solution times such that

`|g_t (gradient R_t) v| <= C * sqrt (g_t v v)`.

The proof applies `gradSq_joint` to scalar curvature, using the solution's
native smooth moving-metric frame components and `scalar_joint`.  Compactness
of the time interval times the compact manifold bounds the square root of the
gradient norm squared.  The final pairing estimate reuses
`abs_metric_inner_le_sqrt_metric_quadratic`; no local inner-product instance or
new bundle comparison API is introduced.

`lRicci_bound` gives a nonnegative constant on the same kind of interval such
that

`|Ric_t(v,v)| <= C * g_t(v,v)`.

It uses the native moving-metric unit-tangent time slab.  Its compactness comes
from `metricUnitTimeSlab_icc_compact_of_bundle`; continuity of Ricci evaluation
comes from the solution's existing `ricciCont` witness through
`timeSlabAbsQuadCont`; and `compactUnitTimeSlab_absBound` extends the unit bound
homogeneously to every tangent vector.

## Verification and frontier

Focused verification passes without warnings or placeholders.  Public names
remain within the twenty-character limit, and no reference-tree module is
imported.

These theorems discharge the compact-slab coefficient assumptions of
`lRegSpeed_gron` and `lRegInit_bdd` after substituting backward times
`t = T - s^2`.  The remaining assembly is to combine their constants, the
existing action-to-kinetic split, and the positive lower endpoint into the
canonical minimizing-ray initial-vector statement.  Convergence stability of
minimizing vectors remains a separate downstream theorem.
