# MetricTrace Norm Bounds

## 2026-07-14

`component_le_sqrt`, `trace_normSq_le`, and `trace_normSq_rank_le` are proved
and focused-check green. The trace bounds control the squared norm of the
first-two-slot metric trace by an explicit finite-dimensional multiple of the
squared norm of the source tensor; the rank-indexed form is the one used by the
Ricci curvature-tower contraction.
The proof uses an orthonormal basis presentation only as a pointwise proof
device; its conclusion is intrinsic.

This is the tensor-layer input for bounding covariant Ricci towers by
covariant Riemann towers.  That geometric identification remains downstream;
it is not part of this file's theorem completion.
