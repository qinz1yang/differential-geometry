# HeatKernelLinear

## Status

Source-written on 2026-07-19; focused Lean verification is pending while the
shared named build owns the build lane.

## Mathematical content

`linD2Cancel` defines the frozen-coefficient heat cancellation operator by
conjugating `heatD2Cancel` with an arbitrary finite-dimensional continuous
linear equivalence `L`.  `linPull_holder` proves that pulling back
exponent-`1/2` data costs `‖L‖^(1/2)`.  `linD2Cancel_op` adds the two inverse-map
norms associated with the two derivative directions.

This avoids an unnecessary determinant-normalized kernel and is the intended
bridge from the isotropic Gaussian estimates to a frozen positive inverse-Gram
principal matrix.  The next geometric producer must construct the relevant
square-root equivalence and bound `‖L‖`, `‖L⁻¹‖` from the existing
`ellMin`/`ellMax` constants.
