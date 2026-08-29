# ActionWeakEuler

## Result: verified nonlinear weak Euler equation

`lChartAct_line` and `lChart_weak_euler` are now focused-green without
warnings or placeholders. The first theorem differentiates the genuine
curve-dependent chart L-action along an affine `timeH1` line whose compact
unit tube remains inside the chart target. The second derives the native weak
Euler identity from an actual `IsLocalMinOn` on `sameTimeEnds u`; it does not
assume stationarity, a supplied force equation, or the desired regularity.
The public derivative returned by `lChartAct_line` is written directly with
`chartGramOp`; the private dominated-differentiation coefficient no longer
leaks through the exported theorem type, so boundary-variation consumers can
rewrite the kinetic term without unfolding an inaccessible implementation
detail.

The scalar-value performance boundary was closed by avoiding a fresh
`ContDiffOn infinity` reduction. The proof packages `hS.scalarCont` as the
existing `ScalarSTContOn` predicate, moves the time coordinate into the
carrier subtype, and reuses the compiled `continuous_subtype` theorem. The
chart inverse is composed on the compact affine tube, and the final weight is
multiplied only after this subtype composition. This introduces no new
wrapper or assumption.

The generic helper `cont_zero_slice` keeps zero-parameter coefficient slices
in lambda normal form. The remaining coefficient proof uses the native
`prodMk` measurability API, explicit pointwise congruences, and two elementary
quadratic estimates for the common domination bound. The Gram derivative is
still fully evaluated on two velocities; no whole-Hom comparison is used.

Focused verification and the required targeted module refresh both passed.
The scoped heartbeat budgets remain local to the declarations whose compact
tube and dominated-integral proof terms are expensive to elaborate.

## Project position

`lChartAct_line` and `lChart_weak_euler` are each 100% verified. Their
dedicated weak-Euler machinery is 100% for the stated interfaces. The next
corner theorem `lNode_mom_match` remains 0%; it must use the checked
shared-node recovery and may not assume momentum matching or add a cotangent
transition wrapper. The terminal regular `exists_lMinimizer` and
`redVolume_anti` remain 0%. Dedicated L-geometry is about 87--89%; P2 remains
below 1%, and the whole Poincare program remains about 3--5%.
