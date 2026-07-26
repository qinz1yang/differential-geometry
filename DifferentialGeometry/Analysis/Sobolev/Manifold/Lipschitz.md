# Lipschitz

## 2026-07-16 qualitative chart entrance

`mem_chart_one_of_lip` is the first nonsmooth manifold-side entrance needed
by distance cutoffs.  A bounded function that is globally Lipschitz for
`riemannianEDistOf g` has first-order chart Sobolev membership for every
exponent `p ≥ 1`.

The proof uses the zero-extended weighted chart function
`chartPushedRaw I α (ρ_α · u)`, not the literal global `chartPushed`, whose
extended-chart junk value need not vanish off the chart target.  On the
support, `chart_inv_edist_le` controls the inverse chart after the metric from
`g` is installed locally; the smooth POU factor is locally Lipschitz.  Off the
support, the raw extension is locally zero.  Compact support and the amplitude
bound then globalize the Euclidean Lipschitz estimate through
`lip_of_local_comp`, after which
`memWkp_one_of_lip` and a.e. congruence give `MemWkpChart`.

This is qualitative infrastructure only.  Its existential chart Lipschitz
constant is metric- and chart-dependent and does not supply the universal
intrinsic `O(1/r)` weak-gradient bound required by Perelman's cutoff energy
estimate.

Focused verification and the targeted module build passed.  The qualitative
chart entrance is complete, and the later intrinsic weak-gradient assembly now
preserves the input's exact Lipschitz constant.  The remaining quantitative
step is narrower: for a Lipschitz input minus a smooth approximant, bound the
intrinsic gradient error by the existing chart-W¹ error.  This is the bridge
needed to consume chart density without losing the tent's scale-order energy.
