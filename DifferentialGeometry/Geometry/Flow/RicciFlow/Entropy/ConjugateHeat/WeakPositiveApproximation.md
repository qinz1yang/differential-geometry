# Positive smooth tests for weak W1,2 data

Current acceptance2026-09-10: saved check2 EMPTY; named build1 PASS; fresh20-public WeakEntropyAxioms1 contains only standard axioms. Source/artifact hashes and exact receipts: E:/lean-tools/chapter25-book-20260910/weak-entropy-completion.json. The preparation notes below are historical.

2026-09-10 Chapter25 source-only work; independent verification is pending.
Claim257d5ba1-abe8-4846-a14f-1236bf21f862 (shared with SmoothEntropyNormalization).

Combine normalized smooth approximation with the existing exists_pos_wform.
Each step uses half the requested error. Nonemptiness of the manifold follows
from the actual unit mass hypothesis, so no public nonemptiness assumption is
introduced. The output has its actual smooth gradient, strict positivity,
unit mass and an upper bound on the actual W integral. Chapter25 can import
this producer without changing EntropyTest or creating an import cycle.
