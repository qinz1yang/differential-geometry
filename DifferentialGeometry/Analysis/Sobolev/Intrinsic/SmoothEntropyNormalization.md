# Normalization in weak entropy approximation

Current acceptance2026-09-10: saved check4 EMPTY; named build1 PASS; fresh20-public WeakEntropyAxioms1 contains only standard axioms. Source/artifact hashes and exact receipts: E:/lean-tools/chapter25-book-20260910/weak-entropy-completion.json. The preparation notes below are historical.

2026-09-10 Chapter25 source-only work during the Chapter23 compiler window.
Claim257d5ba1-abe8-4846-a14f-1236bf21f862 (shared with WeakPositiveApproximation).
Independent verification is pending; no endpoint is counted as closed.

Use the four convergent integrals from WeakEntropyApprox. Multiplication of
a smooth function by c scales mass and energy by c^2 and adds the exact
c^2 log(c^2) mass term to the entropy. The identity follows from the native
negMulLog product formula, including zeros. The inverse square root of the
approximating mass converges to one. Eventually the mass is positive, so one
obtains a genuinely normalized smooth test with arbitrarily small W error.
The input remains the actual weak gradient and its metric L2 norm.

The source does not require a nonnegative weak representative or positive tau;
those are only needed, where relevant, by the later positive smoothing step.
