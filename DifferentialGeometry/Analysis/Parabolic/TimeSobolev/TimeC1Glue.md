# C1 time gluing

## Result

`contDiffOn_Icc_join` is the generic one-dimensional closed-interval gluing
lemma needed after a corner condition has been proved.  For a single assembled
function, it combines `C¹` regularity on two positive adjacent intervals and
equality of the two one-sided `derivWithin` values at their common node into
`C¹` regularity on the full interval.

The proof uses Mathlib's native `HasFDerivWithinAt.union`.  It constructs the
continuous derivative by gluing the two `fderivWithin` fields and does not
assume momentum matching, Euler equations, or any geometric regularity.

## Boundary

This is only the routine analytic gluing step.  In Perelman L-geometry the
genuine remaining variational frontier is the crossing-node corner condition
(`lNode_mom_match`): independent fixed-endpoint minima on the two segments do
not imply equality of their node velocities.

Focused verification passed without warnings.  The generic gluing theorem and
its dedicated analytic machinery are complete (100%).  The separate geometric
corner theorem remains unstated and therefore 0%; this module does not advance
that variational frontier by itself.  The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; the source has no placeholder or new
axiom.
