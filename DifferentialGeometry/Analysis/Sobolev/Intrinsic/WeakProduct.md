# Weak-gradient localization for Chapter 25, Lemma 25.3

## Accepted verification,2026-09-10

Final saved source: focused EMPTY 21.18s; named build 31.37s.
Fresh28-public audit21.61s completed17:52:36UTC: standard axioms only.
Source SHA256: 823ef66a14fa7839fa219fb4b46ae7a336d19df6107f5e0c3c97d9242ff0c9fe.
Receipts: E:/lean-tools/chapter25-book-20260910/sobolev-completion.json.
Earlier pending/source-only statements below are historical. No full Lemma25.3
completion claim: gradient-energy convergence and equality of infima remain open.


2026-09-10: source work under claim fa638d52-3e15-4482-9859-8072221f3d7e.

`HasWeakRiemannianGradLp.smooth_mul` tests the actual weak gradient against
`smoothSmul φ X`, applies the native divergence product rule, and splits the
integrals only after proving their integrability. Its gradient is
`φ G + u grad φ`; G has no smoothness assumption. The pairing-integrability
lemma reuses the existing metric Cauchy--Schwarz inequality.

`MemW1pIntrinsicLp.smooth_mul` also supplies the full weak Sobolev membership:
the mixed pairing with the smooth gradient gives measurability of the product
gradient's energy, and the native metric norm triangle inequality gives its Lp
bound. Thus measurability is proved rather than added as a caller obligation.

This is a localization step, not the chart weak-derivative or smooth-density
endpoint. The eventual Chapter25 consumer still needs weak-to-chart conversion,
Sobolev embedding for the actual weak function, and entropy convergence.

Source-only during Chapter23's 16:18--17:10 UTC window. Verification pending
an actual shared-window grant, then focused check, named refresh and fresh
external axiom audit. Existing smooth equivalence modules remain read-only.
