# ActionNodeMatch

## Result

`lNode_mom_match` is verified.  It proves the scalar covector form of the
Weierstrass--Erdmann corner equation for two positive consecutive L-action
pieces written in different manifold charts.  The right momentum is paired
against `tangentCoordChange` of the left test vector, so the statement neither
compares bundle-valued objects nor introduces a cotangent wrapper.

The public assumptions are the original two chart representatives, strict
positivity of both pieces, regular backward times, and the global fixed-endpoint
`C¹` comparison.  Continuity of the manifold curve, local minimality of the
right piece, coordinate `C¹` regularity, and momentum representatives are all
derived internally.

## Proof route

1. `lNodeAct_min` turns global fixed-endpoint minimality into exact two-piece
   chart-action comparison.
2. `lNode_piece_min` and `lChart_mom_c1` make the original right coordinate
   representative `C¹`; `curve_c1_local` transfers this to the manifold curve.
3. `exists_chart_head` chooses a positive right-hand head inside the left chart.
   `chartTimeH1` realizes that head in the left chart and the unchanged tail in
   the original right chart.
4. `lNodeHead_min` cancels the tail, and `lNode_mom_same` gives equality of the
   two left-chart Gram momenta.
5. `chartDeriv_head` transports the head derivative to the original right
   representative; `chartGramOp_change` gives the final scalar pairing identity.

The implementation reuses only native `DifferentialGeometry` APIs.  No
reference-tree import, `sorry`, new class, or stronger consumer assumption was
added.

## Verification and progress

Focused verification passed without warnings.  The cross-chart node-momentum
theorem is 100% complete; its dedicated corner machinery is 100% for this
interface.  The next regularity consumer is the velocity-matching/gluing step.

This closes one regularity brick, not the global capstone:
`exists_lMinimizer` remains 0%, `redVolume_anti` remains 0%, dedicated
L-geometry machinery is approximately 89--91%, P2 remains below 1%, and the
whole Poincaré program remains approximately 3--5%.
