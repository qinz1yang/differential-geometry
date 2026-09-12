# Smooth approximation of the four entropy integrals

Current acceptance2026-09-10: saved check1 EMPTY; named build1 PASS; fresh20-public WeakEntropyAxioms1 contains only standard axioms. Source/artifact hashes and exact receipts: E:/lean-tools/chapter25-book-20260910/weak-entropy-completion.json. The preparation notes below are historical.

2026-09-10 claimdbb641d4-da71-4908-9a84-e7f71294a765. Source-only in the
Chapter23 compiler window; all new dependencies are also pending verification.

Combine weak metric L2 density, continuity of scalar/weighted quadratic
integrals, and the uniform subcritical Sobolev bound. The same smooth sequence
has bounded scalar and gradient L2 norms, hence bounded Lq norm for a fixed
q>2. Select an a.e. scalar subsequence via convergence in measure. Fatou puts
the given weak function in that same Lq exponent; EntropyUniform passes the
actual entropy integral. The result leaves mass normalization and positive
smooth replacement to the Chapter25 consumer. Neither of those conclusions is
included as an assumption.
