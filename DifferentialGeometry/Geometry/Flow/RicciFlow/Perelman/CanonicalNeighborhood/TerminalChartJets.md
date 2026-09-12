# TerminalChartJets

Verified 2026-09-09: focused2 EMPTY (31.89s), named1 clean (47.34s),
fresh endpoint audit1 standard-only (30.74s). Receipts:
E:/lean-tools/chapter25-terminal-local-20260909/.

Actual closed-carrier flow assumptions produce uniform convergence of every spatial Gram-coefficient jet on one fixed chart neighborhood to the original terminal metric. The proof uses TerminalMetricTimeControl, native `chartJet_sub_le`, then finite-order uniform-Cauchy identification from TerminalJetLimits. The finite order is arbitrary but fixed for each application; no assumed terminal regularity or limit metric is introduced.

The chart Gram basis is `chartModelBasis`, not `Module.finBasis`. Preserve that distinction when connecting the actual coordinate Ricci RHS. The original `cone_terminal_exclusion` remains open until that continuity and the cone evolution assembly are checked.
