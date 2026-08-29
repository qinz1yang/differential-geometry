# ActionNodeRefine

## Result

`lNodeRef_cmp` is complete and focused verification passes without warnings or
placeholders.  It refines an arbitrary finite node window by inserting a
strictly interior time `c` into the old right segment, preserving the complete
finite chart-`H¹` realization needed by `lNodeWin_cmp`.

The selected refined pair is the unchanged left piece followed by the supplied
short right head in the left chart.  The complementary part of the old right
piece is constructed with `timeH1.slice` and remains in the old right chart;
all other pieces, charts, source conditions, representations, endpoints, and
monotonicity data are transported unchanged.

The adapter introduces no new class or frontier hypothesis.  The only caller
input beyond the old finite realization is the short head realization and the
two strict inequalities placing `c` inside the right segment.  The final action
comparison is obtained by applying the existing `lNodeWin_cmp` theorem to the
refined realization.

## Lean details

The implementation uses `Fin.insertNth` and `Fin.succAbove` for the inserted
node and chart indices.  Dependent `timeH1` transports are kept scalar: the one
non-definitional index transport is proved through `Sigma.mk` equality and
`eqRec_heq`, without unfolding `timeH1` or bundle representations.

## Progress

- `lNodeRef_cmp`: 100% (proved and focused GREEN).
- The noncompact declaration-level recheck is warning-free green: the theorem
  exports without `CompactSpace M` because all compactness is carried by its
  supplied finite chart data. Its downstream refresh also passed.
- Caller-side finite right-piece refinement adapter: 100%.
- Dedicated finite-node comparison machinery: about 99%; downstream assembly
  still has to consume this exported theorem.
- Dedicated L-geometry machinery: about 93%.
- `exists_lMinimizer`: 0% (not stated/proved here).
- `redVolume_anti`: 0%.
- P2 endpoint: below 1%; full Poincaré project: about 3--5%.

## Next exact consumer

Instantiate `lNodeRef_cmp` from the finite-node regularity layer after choosing
the positive split and constructing its left-chart `timeH1` head.
