# Distances

## 2026-07-13 alignment verification

The latest progress moves the reusable `speed_le_of_c0` and
`data_image_ball` producers from `StepDDirected.lean` into this canonical
distance layer.  After the short-time-existence merge, the tensor subtraction
step was adapted to the public `Tensor0SSpace.sub_apply` API.  The theorem
statements are unchanged, and focused verification passed without warnings.

## Source

MSM135 Chapter 4, Proposition "Distances" proves that an
`(epsilon,0)` pre-approximate isometry sends a `g`-ball of radius `r` into the
`h`-ball of radius `sqrt (1 + epsilon) * r`.

## This pass

The implemented theorems now include the F2 route at the path-speed-bound
level. `pathComp_tangent` turns a target-path producer with pointwise
Riemannian speed bound into the smooth path-length comparison used in the book.
`edist_le_of_path_comp`, `dist_le_of_path_comp`, and
`image_ball_subset_of_path_comp` turn that path comparison into distance and
ball-inclusion statements. The direct consumers `dist_le_tangent` and
`image_ball_tangent` package Proposition "Distances" from the path-speed bound.
The older metric-space wrappers `lipschitz_sqrt_of_dist_le` and
`image_ball_subset_of_lipschitz_sqrt` remain as smaller consumers.

## Remaining frontier

The book-facing distance producer is complete for a localized
`PreApproxIsoDataOn` package with the explicit metric/enorm readouts consumed by
`data_image_ball`.  Producing those packages uniformly in the B1 construction
remains a separate endpoint frontier; it is not hidden in this file.

## Verification

Verification passed for the targeted `Distances` file, its downstream
`StepDDirected` consumer, and the aligned full build.
