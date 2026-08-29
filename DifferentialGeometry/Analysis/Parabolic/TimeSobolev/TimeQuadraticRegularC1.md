# C1 momentum regularity

## Result

`primitive_c1` proves directly from the interval-integral fundamental theorem
that a constant plus the primitive of a continuous Banach-valued force is
`ContDiffOn ℝ 1` on `[0,T]`.  Its `derivWithin` is the force at every point,
including the natural one-sided derivatives at the endpoints.

`mom_rep_c1` consumes the actual zero-endpoint time-`H¹` weak Euler identity.
It combines `mom_primitive_l1` with `primitive_c1`, so the momentum agrees
almost everywhere with a closed-interval `C¹` representative whose derivative
is the continuous force.  It does not take an Euler equation, primitive
representation, or regularity conclusion back as an assumption.

## Assumptions and boundary

The primitive theorem needs only a complete real normed space.  Finite
dimensionality and the inner product enter only through the existing weak-Euler
to primitive theorem.  The result is a within-set `C¹` statement; it does not
claim a two-sided endpoint derivative or extend the force outside `[0,T]`.

## Status and project position

Focused verification and the exported-module refresh passed without warnings.
Both public theorems are
complete (100%), and the dedicated continuous-force momentum upgrade in this
module is complete (100%).  This is generic Tonelli bootstrap infrastructure;
the terminal Perelman `exists_lMinimizer` and `redVolume_anti` endpoints remain
0% until they are stated and proved.  Dedicated L-geometry remains roughly
80--84%, while the whole Poincare program remains roughly 3--5%.

The source contains no `sorry`, `admit`, or new axiom.
