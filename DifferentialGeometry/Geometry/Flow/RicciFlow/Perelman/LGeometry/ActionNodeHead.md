# ActionNodeHead

## Purpose

This module transfers a global fixed-endpoint `C¹` minimality comparison to
two consecutive `timeH1` pieces represented in one chart, while retaining an
unchanged third tail represented in a possibly different chart.

The proof realizes the two-piece competitor with `lNode_c1_dense`, joins it to
the original tail, applies `lAction_c1_dense` to the resulting three-piece
curve, and cancels the identical tail after two applications of
`lRegAction_chart_sum`.  Thus it introduces no chart-transition assumption or
consumer-side frontier.

## Status

Focused verification and the targeted module refresh passed without warnings.
The target `lNodeHead_min` is 100% complete.  Its public statement uses only
the three segment source and representative hypotheses; it does not require
the baseline curve to be globally continuous.

The dependent `Fin 3` action family required explicit successor-index
normalization at the final three-term sum.  This is an elaboration detail, not
an additional hypothesis.  The theorem is the local comparison bridge needed
before proving the cross-chart corner momentum identity.

Project accounting: `lNodeHead_min` is 100%; the cross-chart corner momentum
theorem remains 0% until stated and proved; its dedicated node machinery is
about 96--98%.  Dedicated L-geometry remains about 87--89%, while
`redVolume_anti` remains 0%, P2 remains below 1%, and the whole Poincare
program remains about 3--5%.
