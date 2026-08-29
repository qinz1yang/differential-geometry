# ActionStrictC2

## Role

`lStrict_piece_c2` is the strict finite-piece Tonelli bootstrap. Given the
same finite chart-`H¹` realization and genuine global fixed-endpoint minimum
used by `lStrict_piece_c1`, it proves that every coordinate representative is
`C²` on its closed piece interval.

Strictness supplies the positive segment length. Global minimality descends to
the actual fixed-endpoint chart minimum through `lChartAct_local`.
`lChart_min_c1` supplies a continuous weak-velocity representative, the native
`lChart_weak_euler` supplies the genuine weak Euler identity, and
`lChartVel_c1` upgrades the coordinate velocity to `C¹`. Unique
differentiability of the nondegenerate closed interval then gives `C²` for
the coordinate curve.

`lStrict_piece_c2_at` is the manifold-valued interior form used by later
regularity consumers.  It reconstructs the curve through the inverse extended
chart, transports the coordinate `C²` statement through the affine time shift,
and then uses germ equality on the open piece.  This keeps the reconstruction
in the same layer as the coordinate producer instead of duplicating it in the
node and whole-interior modules.

No Euler equation, velocity regularity, or C² conclusion is assumed by the
public theorem.

## Verification and progress

Focused verification passed without warnings or placeholders. The exported
module was refreshed for downstream consumers.

The focused noncompact recheck also passed without warnings. Both
`lStrict_piece_c2` and `lStrict_piece_c2_at` now export without an ambient
`CompactSpace M` instance. Their downstream refresh passed.

The terminal `exists_lMinimizer` and `redVolume_anti` remain 0%. The strict
finite-piece coordinate and manifold-valued C² producers and their local-
minimum-to-Tonelli assembly are 100%.
Dedicated minimizer/direct-method machinery is about 97--98%, while dedicated
L-geometry machinery is about 94--96%; reused generic infrastructure for this
brick is 100%. This local theorem does not itself establish global minimizer
existence, node matching, or reduced-volume monotonicity. P2 remains below 1%,
and the whole Poincare program remains about 3--5%.
