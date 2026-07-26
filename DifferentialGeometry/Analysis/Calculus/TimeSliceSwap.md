# TimeSliceSwap.lean

## Purpose

`hasDerivAt_iterF` commutes a pointwise time evolution equation with any fixed
finite spatial Fréchet derivative.  Its hypotheses deliberately avoid joint
differentiability of the evolving family: only smooth spatial slices and joint
continuity of the required spatial jets of the right-hand side are used.

## Current status

The implementation uses a local interval FTC argument and differentiation under
the interval integral.  Compactness is used only in the time variable, so no
finite-dimensional assumption on the spatial model is required.  Completeness of
the target is required by the Banach-valued FTC.

Focused verification passes.  The only delicate implementation point is the
successor step: currying an integrated Fréchet derivative is handled by commuting
both the inner continuous-linear-map evaluation and the outer multilinear-map
evaluation with the interval integral.  This keeps the proof independent of
definitional unfolding of the currying equivalence.
