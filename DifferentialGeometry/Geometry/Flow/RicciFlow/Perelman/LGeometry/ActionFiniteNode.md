# Finite-node L-action velocity

## Goal

`lFinNode_vel` should show that every internal node of a positive finite
chart-`H¹` realization satisfies the tangent-coordinate velocity matching law,
using only the global fixed-endpoint `C¹` comparison property already produced
by relaxed attainment.

## Route

The selected right piece first inherits a genuine local chart-action minimum
from `lChartAct_local`, hence `lChart_min_c1` makes it `C¹`.  A strictly shorter
initial head is then represented in the left chart.  `lNodeRef_cmp` gives exact
left/head comparison inside the full finite realization, and
`lNode_mom_same` gives the same-chart endpoint momentum identity.  Finally
`chartDeriv_head` transports the head derivative to the original right chart;
`chartGramOp_change` and `chartGramOp_unit` cancel the metric Gram operator.

## Verification

Focused verification and the exported-module refresh passed without warnings.
The file contains no `sorry`, `admit`, new axiom, reference-tree import, or
additional consumer assumption.

The focused noncompact recheck also passed without warnings. `lFinNode_vel`
now exports without an ambient `CompactSpace M` instance after the local and
two-piece comparison producers were generalized. Its downstream refresh
completed successfully; an unrelated pre-existing unused-section-variable
warning remains in `ActionNodeLocal`.

The theorem itself and its finite-node comparison route are complete.  The
next exact consumer is the finite strict-piece C¹ assembly: combine
`lStrict_piece_c1`, `lFinNode_vel`, and `curve_c1_fin` to obtain global C¹
regularity of the strict realization.  `redVolume_anti` and the terminal
`exists_lMinimizer` remain 0%; dedicated L-geometry machinery is approximately
93--95%, while the generic infrastructure used by this theorem is complete.
