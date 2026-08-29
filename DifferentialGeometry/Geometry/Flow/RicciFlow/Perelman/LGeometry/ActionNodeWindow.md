# ActionNodeWindow

## Result

`lNodeWin_cmp` localizes the global fixed-endpoint `C¹` comparison of a
finite-chart-`timeH1` relaxed minimizer to any adjacent positive two-piece
window.  The public index `q : Fin (m + 1)` selects the two segment indices
`q.castSucc` and `q.succ`, so their shared subdivision node is definitional
rather than transported through an equality of dependent interval lengths.

The conclusion is the exact two-chart action inequality for arbitrary
target-contained replacements with the same outer manifold endpoints and a
common inverse-chart node.  It assumes neither stationarity, momentum matching,
nor regularity of the relaxed curve beyond its existing continuous finite-chart
realization.

## Route

The theorem first applies `lNode_c1_dense` to the two replacement pieces.  It
splices the resulting continuous window curve into the original curve and
represents the result by the doubly updated finite `timeH1` family.  Every
segment before or after the window is unchanged, including at the two closed
window endpoints.  `lAction_c1_dense` then supplies global fixed-endpoint `C¹`
competitors, so global minimality passes to the spliced curve.  Two exact
`lRegAction_chart_sum` identities and finite-sum cancellation remove the
unchanged prefix and tail.

This theorem is deliberately general over the whole finite realization, not
tied to the original chart pair.  After inserting the short right-hand head
used in the cross-chart corner proof, the same theorem applies to the refined
adjacent pair with charts `p0, p0`; the following `p1` tail is simply one of the
unchanged pieces.  Thus no second variational localization theorem is needed.

## Boundary

The theorem produces the exact chart-`H1` comparison actually consumed by the
node regularity and corner calculations.  It does not claim the stronger
statement that the relaxed window is minimal against every arbitrary global
`C¹` curve on that window: such a curve may leave both selected charts, and
proving that statement would require a new finite chart cover and endpoint-flat
recovery for the arbitrary competitor.  Adding that stronger interface here
would not be a thin localization lemma.

Both selected segments must have positive length.  A later subdivision
compression removes repeated nodes and supplies a strictly increasing list;
each internal node of that compressed list then gives a valid `q` and the two
strict-window hypotheses required here.  No property is asserted for a
zero-length segment before compression.

## Verification and progress

Focused verification passed without warnings or placeholders.  The public
name has twelve characters and the theorem uses no new class, axiom, or
reference-tree import.

The focused noncompact recheck also passed without warnings. `lNodeWin_cmp`
now uses the generalized two-piece density producer and exports without an
ambient `CompactSpace M` instance. Its downstream refresh also passed.

- `lNodeWin_cmp`: 100% for its exact comparison interface.
- Arbitrary positive-window variational localization machinery: about 98--99%;
  the remaining work is the caller-side finite resegmentation adapter.
- Dedicated L-geometry machinery remains about 91--93%.
- Terminal `exists_lMinimizer`: 0% until stated and proved.
- `redVolume_anti`: 0%; P2 remains below 1%, and the whole Poincare program
  remains about 3--5%.
