# ActionNodeC1

## Target

`lNode_c1` upgrades the positive two-piece corner regularity theorem from
chartwise `C¹` to global manifold `C¹` regularity across the shared node.

The proof derives local minimality of each chart piece from the exact two-piece
comparison, applies `lChart_min_c1`, transports `lNode_vel_match` into the chart
centered at the node, and applies the generic `curve_c1_join` theorem.  It adds
no regularity, momentum, or corner hypothesis.

Repeated nodes and zero-length pieces are intentionally outside this positive
two-piece theorem; finite-node assembly must compress them before applying it.

## Status

Focused verification passed without warnings, and the exported module refresh
is green.  The source contains no `sorry` or `admit`.

`lNode_c1` and its dedicated positive two-piece gluing machinery are complete
for this interface (100%).  This closes the local corner-regularity brick, not
the direct-method endpoint: terminal `exists_lMinimizer` and
`redVolume_anti` remain 0%.  Dedicated L-geometry machinery is approximately
91--93%; P2 remains below 1%, and the whole Poincare program remains
approximately 3--5%.
