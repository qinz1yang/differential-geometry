# TerminalMetricTimeControl

Verified 2026-09-09: focused2 EMPTY (32.99s), named1 clean (50.82s),
fresh two-public audit1 standard-only (30.60s). Receipts:
E:/lean-tools/chapter25-terminal-local-20260909/.

Adapts native `ric_bound_const` and `timeLipschitz_of_hasDerivAt` on a compact subset of an open local buffer. The zero-order case uses pointwise norm comparison; higher orders use the native affine Ricci-tower estimate. All derivative statements concern strict regular times.

The local endpoint assembles the common buffer using the verified
TerminalLocalBounds/TerminalCovariantBounds producers. Next: apply
`chartJet_sub_le` and identify actual terminal jets by TerminalJetLimits.
This is not yet the terminal Ricci RHS continuity theorem.
