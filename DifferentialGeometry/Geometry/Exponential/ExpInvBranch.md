# ExpInvBranch

## 2026-07-24 fixed-first branch interface

`ExpInvBranch` is the canonical fixed-base inverse object selected by the
Calabi distance-support architecture.  It stores one `C∞`
`PartialDiffeomorph` from the model tangent fiber to the manifold and equality
of its forward map with the intrinsic exponential on the open source.

The basic fixed-first API consists of `inv`, `dom`, `left_inv`, `right_inv`,
and `inv_inf`.  `branch_of_not_conj` now constructs such a branch from
nonconjugacy by the manifold inverse function theorem, while
`ExpInvBranch.not_conj` gives the converse on the selected open source.
The chart bridge `hasFDerivAt_chart` records that composing with the centered
target chart preserves the intrinsic manifold derivative.  The source file is
focused-green without local warnings and contains no placeholder.

The proof first obtains a `C¹` branch at the selected vector, uses that branch
to recover derivative invertibility throughout its open source, and then
upgrades once to a `C∞` partial diffeomorphism.  Quantitative source radii,
injectivity radii, and endpoint assumptions are intentionally absent.

The target `calabiDist_support` theorem remains unproved (0%).  This file is
one completed reusable branch/IFT brick in its dedicated fixed-metric
machinery; it does not by itself advance the theorem-level endpoint above 0%.
