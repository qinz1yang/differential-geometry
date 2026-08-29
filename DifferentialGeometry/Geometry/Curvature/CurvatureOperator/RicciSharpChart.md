# `RicciSharpChart.lean`

## Goal

Provide the reusable fixed-trivialization finite-sum representation of
`ricciSharp` needed by coordinate ODE regularity arguments.

## Route

The proof uses the native `trivToE_metricSharp` inverse-Gram formula and
`chartBasisVecFiber_recompose` to expand only the first Ricci slot.  It does not
unfold dependent total spaces or introduce a realization predicate.

The successful elaboration keeps the round-trip equality
`trivFromE (trivToE v) = v` local to the auxiliary covector family.  Rewriting
that equality across the whole goal also rewrote the coordinate occurrence of
`v` on the right-hand side and produced an unusable nested expression.  The
component expansion instead rewrites only the left-hand Ricci slot.

## Verification and project status

Focused verification passes without warnings or placeholders.  The public
theorem `ricciSharp_chart` and this chart-representation brick are complete
(100%).  `exists_lAdapted` remains unstated and unproved (0%); its dedicated
coefficient-regularity machinery now has the previously missing lower-layer
Ricci-sharp representation, but the consumer proof has not been retried here.

This is a small lower-layer brick in the adapted-field phase.  The explicit
trace contraction and Morgan--Tian Laplacian inequality remain unstated and
unproved (0%), as does `redVolume_anti`.  Compact ordinary-flow L-geometry
machinery remains about 99%, P2 remains below 1%, and the whole Poincare program
remains approximately 3--5%.
