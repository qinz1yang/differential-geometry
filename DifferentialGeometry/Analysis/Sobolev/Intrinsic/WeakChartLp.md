# Local Lp transport for weak Sobolev functions

## Accepted verification,2026-09-10

Final saved source: focused EMPTY 19.47s; named build 50.22s.
Fresh28-public audit21.61s completed17:52:36UTC: standard axioms only.
Source SHA256: 92bc330864f94940a407be71bc839249ae477ae6a4bbed9abc188a23ae56d300.
Receipts: E:/lean-tools/chapter25-book-20260910/sobolev-completion.json.
Earlier pending/source-only statements below are historical. No full Lemma25.3
completion claim: gradient-energy convergence and equality of infima remain open.


2026-09-10, claim b315c09c-b34e-4a34-9724-89524648de66. Chapter25 Lemma25.3
needs chart Lp estimates for genuinely weak functions. The existing quantitative
MeasureBridge estimates require measurable representatives. This leaf transports
actual MemLp data, including its almost-everywhere measurability, through the
chart-local measure. A positive lower bound for the Riemannian density on the
compact support removes the weight. The conclusion uses the existing chart
functions and actual Euclidean volume; no extra measurability field is added
to EntropyTest.

Source/verification work in the explicitly granted16:50--18:00 UTC window.
No endpoint completion claim until saved focused check, named refresh and fresh
external axiom audit. Following work: coordinate weak-gradient Lp control and
MemWkpChart, then genuine smooth approximation and entropy relaxation.
