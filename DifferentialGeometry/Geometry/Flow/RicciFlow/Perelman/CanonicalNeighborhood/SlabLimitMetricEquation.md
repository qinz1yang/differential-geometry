# SlabLimitMetricEquation

FINAL ACCEPTANCE 2026-09-10 00:40UTC: landed in scoped local commit82d2a5ff7.
Saved EMPTY check, named lint build and fresh standard-only public axiom audit
all passed for the current source. The ordinary source claim is released.
Reproducible hashes and receipts: E:/lean-tools/chapter25-terminal-local-20260909/slab-equation-completion.json.
The dated notes below retain the proof route and iteration evidence.

2026-09-10 00:29UTC: independent saved check120 passed with empty compiler
diagnostics (22.08s); named refresh120 passed (29.39s), with only the two known
Chapter25Convergence warning replays. Fresh stable-batch public audit pending;
ordinary claim ad574ad7 retained in the granted Chapter25 window.

Target: the actual interior metric equation for a family satisfying IsSlabLimit.
Use SlabMetricCoefficientLimit for pointwise metric-value convergence and
SlabRicciCoefficientLimit for uniform Ricci coefficient convergence on a compact
time window around an interior time. Every source solves the equation there by
StaticTerminalLimit.regular_window. Native hasDeriv_lim_tail gives the limit
derivative; interior membership upgrades it to HasDerivAt.

Keep source and limit metrics, selected indices and the original terminal map
differentials explicit. Do not add a limit-PDE or limit-IsSolutionOn hypothesis.
The full IsSolutionOn construction still needs joint regularity and scalarTime
on the carrier. Proof of the metric equation alone does not close that interface.

The source derivative already contains the actual tensor evaluation. Preserve
that elaborated expression: dsimp only [SolutionOn.ricciAt,
SolutionFamily.ricciAt] at the derivative, then erw with the fully instantiated
metricRicciAt_apply_eq_ricciTensor equality. A generic simp did not reconcile
the dependent source evaluation, and reconstructing its Tensor02At application
triggered a CoeFun inference failure. No additional differentiability hypothesis
or raised heartbeat limit is needed.
