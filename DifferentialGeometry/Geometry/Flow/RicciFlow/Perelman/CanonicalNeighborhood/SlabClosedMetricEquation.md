# SlabClosedMetricEquation

2026-09-10 00:47UTC VERIFIED: first saved check132 EMPTY (20.44s), named
lint build132 passed (27.74s, only the two known Chapter25Convergence warning
replays), fresh audit133 gives two standard-only theorems (72.35s). Ordinary
source claim baf724c3 is released; scoped local commit575ae95d2 landed this leaf
and its own import. One compiler/thread, no REPL. Combined receipt:
E:/lean-tools/chapter25-terminal-local-20260909/slab-closed-equation-completion.json.

Target: the actual metric equation as a HasDerivWithinAt statement on the whole
closed carrier, including the terminal left derivative. Reuse the accepted
SlabLimitMetricEquation and SlabRicciTensorLimit, with the native
Analysis.hasDerivIcc_of_int calculus theorem. The latter requires continuity of
the function and its proposed derivative on Icc and the actual derivative on
Ioo; it derives the endpoint assertion by the fundamental theorem of calculus.

Evaluate the actual continuous limit Ricci tensor at a fixed point and pair of
vectors. Combine this with the accepted metric coefficient continuity and
interior metric derivative. No limit flow, terminal derivative, or extra
regularity assumption may be added. This metric derivative is not scalarTime
and does not close full joint smoothness, Rm04 continuity, or slab extraction.
