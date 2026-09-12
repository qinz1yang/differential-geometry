# Metric L2 limits for the smooth-approximation step

2026-09-10, claim47566888-41d5-4b7c-b040-f67f2c6f92b8. Next book Lemma25.3
step, after the accepted weak Sobolev/entropy-integrability batch.

Use summable scalar L2 norms of metric gradient increments to get a.e.
pointwise summability. At each fixed point, the native positive-definite
bilinear lower bound compares its metric norm with the tangent-space norm,
so completeness gives an actual tangent-vector limit. This avoids imposing
ambient E-valued L2 membership on EntropyTest.gradient. Scalar Fatou then
controls L2 tails; passage through weak pairings and WeakGradientUnique will
identify the limit with the original gradient. The complete construction and
energy convergence are not yet delivered.

Accepted verification 2026-09-10 17:59UTC: saved check2 EMPTY,22.99s;
named build1 PASS,31.94s; fresh external GradientLimitAxioms audit PASS,20.96s,
all three public theorems standard-only. SHA256
5a66fd78d9d569b4944349ea128efd3e29b5077741772d8b144d7844632c16c6.
Receipts/logs in E:/lean-tools/chapter25-book-20260910/. Root import registered.
These conditional sequence lemmas do not yet construct the smooth sequence
for an arbitrary EntropyTest. Following work remains source-only during
Chapter23's granted18:00--19:00 compiler/artifact/root window.
