# Weak Sobolev embedding and entropy integrability

## Accepted verification,2026-09-10

Final saved source: focused EMPTY 22.44s; named build 30.71s.
Fresh28-public audit21.61s completed17:52:36UTC: standard axioms only.
Source SHA256: 9e39aa81318a8cd002a0c747d0efc0ef551c1b3dc8a4a677d67601e4422aefc6.
Receipts: E:/lean-tools/chapter25-book-20260910/sobolev-completion.json.
Earlier pending/source-only statements below are historical. No full Lemma25.3
completion claim: gradient-energy convergence and equality of infima remain open.


2026-09-10, claim906f7ed1-066a-40ed-8ccb-98a82ed68725. Reuses the existing
closed-manifold chart Sobolev inequality after WeakChartSobolev supplies actual
chart membership. An almost-everywhere measurable representative is selected
only inside the proof; the public input remains the intrinsic weak class.

For dimension n>=2 choose p=2n/(n+1), so 1<=p<min(2,n) and the Sobolev
exponent exceeds2. This handles dimension2 without using an invalid critical
embedding. EntropyLp then gives actual integrability of u^2 log(u^2).

This is the first conclusion of book Lemma25.3, not yet the equality of the
Sobolev and positive-smooth entropy infima. Saved-source checks and fresh
axiom audit are required before reporting the conclusion as verified.
