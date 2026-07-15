# RicciControlsRm

## 2026-07-12 branch-alignment compatibility

`ricciDiagAt_neg` now normalizes the negated component through the canonical
`ricciCompAt basis Ric` argument order before using the original diagonal equality. Focused
verification and targeted build passed. This helper and its dedicated finite-dimensional algebra
are complete (100%); no new Hamilton endpoint theorem was proved here.
