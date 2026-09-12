# Coordinate tests for a genuinely weak gradient

## Accepted verification,2026-09-10

Final saved source: focused EMPTY 24.47s; named build 31.11s.
Fresh28-public audit21.61s completed17:52:36UTC: standard axioms only.
Source SHA256: 247a32bc948764e45781b4f9b698fabbad2aeb28658ddac807cd9c63fd5ee5f2.
Receipts: E:/lean-tools/chapter25-book-20260910/sobolev-completion.json.
Earlier pending/source-only statements below are historical. No full Lemma25.3
completion claim: gradient-energy convergence and equality of infima remain open.


2026-09-10, claim e3df38e6-8b40-469e-b890-e740ddd6fd31. Source-only while
Chapter23 holds its current compiler window; scheduled Chapter25 grant starts
17:10 UTC unless an earlier explicit handback arrives in WORKING_STATUS.

For a smooth scalar φ supported inside a chart, `weightedChartTest` is
`(φ / J) e_i`, with J the actual Riemannian chart density and e_i the actual
coordinate tangent basis. The native section support lemma proves global
smoothness. The Voss--Weyl formula then gives divergence `(partial_i φ) / J`.
This is the test field needed to convert distributional Riemannian gradients
to Euclidean weak derivatives, without assuming the function is smooth.

Next: apply the weak pairing identity, use the actual chart/global volume
restriction identity and map-to-Euclidean Haar identity, and establish local
Lp bounds for the resulting coordinate weak derivative. None of these missing
steps is introduced as a new field of `EntropyTest`.

Saved-source focused check, named refresh and external axiom audit pending.
