# ActionStrictC1

## Role

`lStrict_piece_c1` is the finite strict-piece regularity producer.  Given a
strict finite chart-`H¹` realization of a continuous global minimizer, it proves
that every coordinate representative is `C¹` on its entire closed piece
interval.

The proof uses strictness only to obtain positive piece length.  Global
minimality descends to each fixed-endpoint chart piece through
`lChartAct_local`; `lChart_min_c1` then supplies the closed-interval coordinate
regularity.  Chart containment and regular backward time are derived directly
from the finite realization and endpoint order, so no new wrapper assumption
is introduced.

The theorem deliberately does not repeat the local-minimum conclusion in its
public result: that conclusion is already the canonical `lChartAct_local` API.

## Verification and progress

Focused verification passed without warnings or placeholders.  The exported
module was refreshed for downstream consumers.

The focused noncompact recheck also passed without warnings: `lStrict_piece_c1`
now consumes the generalized local-minimum producer without an ambient
`CompactSpace M` instance. Its refreshed export for the remaining regularity
chain is still pending.

This theorem is a dedicated finite-node regularity producer, not the terminal
minimizer or reduced-volume result.  The terminal `exists_lMinimizer` and
`redVolume_anti` remain 0%.  The theorem and its strict-piece local-to-`C¹`
assembly are 100%; dedicated finite-node assembly is about 96--98%, while
dedicated L-geometry remains about 92--94%.  Generic strict-subdivision and
fixed-chart regularity infrastructure reused here was already 100%.  This brick
does not by itself prove the cross-chart node match or global manifold `C¹`
conclusion.  P2 remains below 1%, and the whole Poincare program remains about
3--5%.
