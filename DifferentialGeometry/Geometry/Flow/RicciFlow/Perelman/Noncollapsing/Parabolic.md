# Fixed-terminal-ball parabolic noncollapsing

Owner: Chapter25 task01a07c8d-49fa-7373-9948-022395d0119a.
User-directed book-first restart, 2026-09-10; ordinary source claim fe8e594e.

The primary correspondence is `master05b.tex`, Definition25.1,
`def:scn-three-noncollapsing-predicates` (2). `IsParabolicallyRmControlled`
uses `B.set` at every past time, never `B.setAt s`. The window is the full
closed interval `[t-r^2,t]` and must lie in the actual flow carrier.
The volume conclusion reuses `FlowMetricBall.IsKappaNoncollapsed`.
The spatial and strong scalar definitions remain those in `Predicates.lean`.

`parabolicallyKappaNoncollapsedBelowScale_of_spatially` is the book's
same-kappa, same-scale implication, by evaluation at the terminal endpoint.
`para_parabolic_noncollapse` supplies the missing fixed-ball case of
Lemma25.2, `lem:scn-noncollapsing-scaling`; its two other cases reuse
`para_spatial_noncollapse` and `para_strong_scalar_noncollapse`.
The clock, metric ball, volume and tensor scaling data are the existing
native `paraSolution`, `paraBall` and `backBall` APIs. Only the private
interval arithmetic and fixed-ball curvature transport need new proofs.

The old `IsRmControlled`, `KappaNoncollapsedBelowScale`, `NoLocalCollapsing`
and their moving-ball proofs remain unchanged. There is no unconditional
same-constant equivalence theorem with the new definition. A geometric
comparison would require actual distance distortion and explicit constants.
Chapter25's compactness predicates are spatial and do not require that bridge.

Verification completed in the actual03:54UTC early handback window:
final saved-file check23.28s with empty diagnostics, named lint build31.62s,
fresh external audit22.25s. All eleven publics (three definitions, eight
theorems) use standard axioms only. The first check found only an unused
SigmaCompactSpace hypothesis on the terminal-bound lemma; it was omitted and
the saved file was independently rechecked. No proof failure or new assumption.

The changed Chapter25Entropy consumer passes check26.52s/build128.77s with
only its seven existing placeholder warnings. Its parabolic theorem is
standard-only; eight of its nine theorems retain existing direct/transitive
proof debt. Chapter25Theorems passes focused regression28.83s with eleven
existing placeholder warnings. That regression is not a new endpoint proof
or a full-project build. New aggregate import is under root claim27367158.

Exact hashes, logs and receipts: E:/lean-tools/chapter25-book-20260910/completion.json.
Reproduce with that folder's run-check.ps1/run-audit.ps1, from dev cwd using
the shared E:/testdifferential-geometry/scripts/lake-locked.ps1. Named builds
require a fresh exclusive grant; do not reuse this expired window.
