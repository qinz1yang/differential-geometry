# ActionFiniteC1

## Purpose

`lFinCurve_c1` assembles full closed-interval `C¹` regularity for any nonempty
positive finite chart-`H¹` realization of a global regularized L-action
minimizer.  Its public interface is indexed by an arbitrary positive number of
pieces; the single-piece case needs no node theorem.

## Route

Each coordinate piece is `C¹` by `lStrict_piece_c1`.  For two or more pieces,
`lFinNode_vel` supplies the adjacent chart-velocity identity at every internal
node.  The native
`chartDeriv_shift`, `chartDeriv_change`, and `tangentCoordChange_comp` identities
turn that equality into the node-centered derivative equality expected by
`curve_c1_fin`, which performs the finite manifold-curve gluing.

No extra regularity, transition-map package, or minimizer assumption is added.

## Verification

Focused verification passed without warnings or placeholders.  The exported
module was refreshed for its downstream umbrella consumer.

The focused noncompact recheck also passed without warnings. Both
`lFinCurve_c1_aux` and `lFinCurve_c1` now work without an ambient
`CompactSpace M` instance, using only the generalized piece and node
producers. Their downstream refresh completed successfully; it replayed only
the unrelated pre-existing `ActionNodeLocal` linter warning.

## Progress

`lFinCurve_c1` and its finite positive-realization assembly are 100% complete.
This is finite-realization regularity infrastructure, not `exists_lMinimizer`
or `redVolume_anti`; those endpoints remain 0%.  Dedicated L-geometry machinery
is approximately 94--95%, while P2 remains below 1% and the whole Poincare
program remains approximately 3--5%.
