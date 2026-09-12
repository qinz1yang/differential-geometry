# Entropy moments for Chapter 25, Lemma 25.3

## Accepted verification,2026-09-10

Final saved source: focused EMPTY 12.8s; named build 14.63s.
Fresh28-public audit21.61s completed17:52:36UTC: standard axioms only.
Source SHA256: 02fcf0cda751476cb361da5a69287b1f749bd34009d200f4394559c43845d295.
Receipts: E:/lean-tools/chapter25-book-20260910/sobolev-completion.json.
Earlier pending/source-only statements below are historical. No full Lemma25.3
completion claim: gradient-energy convergence and equality of infima remain open.


2026-09-10: source work under claim fa638d52-3e15-4482-9859-8072221f3d7e.
The pointwise power bound gives integrability of `f log f` from a moment of
order greater than one, and of `u^2 log(u^2)` from an Lq hypothesis with q > 2.
The square-root version does not assume u is positive or normalized.

These are measure-theoretic steps in the book's proof. They do not supply the
missing weak intrinsic Sobolev embedding or smooth approximation, and do not
close `Chapter25.mu_sobolev_relaxation`. `EntropyTest` remains unchanged.

Verification is pending the next explicitly granted shared compiler window.
No compiler or artifact operation during Chapter23's 16:18--17:10 UTC window.
