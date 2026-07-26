# Tensor section bound by components

Status: the pointwise reconstruction interface is proved and exported.

`fiber_sq_le_comps` exposes the already proved finite chart-frame
reconstruction: the intrinsic squared fibre norm of a smooth mixed tensor is
bounded by a uniform non-negative constant times the finite sum of squares of
its partition-of-unity weighted scalar components.

The theorem is a public wrapper around the file's existing private algebraic
reconstruction lemma.  It adds no assumptions and is the pointwise input used
by `h1_lp6_fiber_rs` before finite Minkowski aggregation.

Producer completion: 100%.  There is no remaining blocker in this interface.
