# MetricPreconvWindowGInf.lean

## 2026-06-13

Implemented the first green C-II-final `gInf` brick in the new file.

What landed:
- `metricPreconvNorm`: exposes the pointwise `metricDerivNorm` convergence that
  sits inside `metricPreconvInf`, by reusing `metricPreconv_gInf`,
  `exists_uniform_patch`, `exists_diag_subseq`, and the finite-cover assembly.
- `netNormDiag`: diagonalizes those fixed-time pointwise norm producers over a
  countable time net, producing one master subsequence and one smooth limit
  metric for each net time.
- `windowOfNet`: records the final consumer shape once an all-time
  `Real -> SmoothRiemannianMetric` family is available and agrees with the
  net-time limits.

Verification: focused check and targeted module build passed. Axiom checks for
`metricPreconvNorm`, `netNormDiag`, and `windowOfNet` were clean: only
`propext`, `Classical.choice`, and `Quot.sound`.

Remaining blocker: the all-time `gInf : Real -> SmoothRiemannianMetric I M`
construction is still not implemented. The missing step is the Cauchy/extension
argument from net-time limits plus `hgLip`, followed by smoothness of each
time-slice. This file now leaves that as the single visible frontier instead of
repackaging it as an assumption inside the net-time diagonal.

## 2026-06-13 follow-up

Implemented the all-time `gInf` blocker in the same file.

What landed:
- `metricPreconvFull`: fixed-time producer exposing both pointwise inner
  convergence and pointwise `metricDerivNorm` convergence.
- `netFullDiag`: dense-net diagonal retaining both fixed-time outputs.
- Local routing lemmas: `normSq0S_neg`, `metricDerivNorm_symm`,
  `netCauchyAt`, `fullOfSubseq`, and `infLipOfConv`.
- `windowGInf`: constructs the all-time limit family by per-time fixed-time
  precompactness, proves full master-subsequence convergence from dense-net
  Cauchy control, derives the limit Lipschitz estimate, and feeds `windowOfNet`.

Verification: focused check and targeted module build passed. Axiom checks for
the new public endpoints were clean: only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry` or `admit` remains in this file.

Scope note: `windowGInf` still takes the upstream uniform time-Lipschitz,
boundedness, and lower-bound hypotheses explicitly. This brick closes the
all-time limit-family construction; it does not discharge those Ricci-flow
producer assumptions. Whole HCG compactness estimate: this closes the dedicated
`gInf` blocker, while the broader Chapter 4/HCG pipeline still depends on the
upstream bound producers and later compactness assembly.

## 2026-06-17

Added the named abstract output wrapper needed by the solution-level P3
assembler:
- `WindowGInfOut`, a Prop-valued package around the final window convergence
  existential;
- `windowGInfOut`, a thin checked wrapper around the existing `windowGInf`.

This is an API/performance boundary only.  It does not change the mathematics
inside `windowGInf`; it gives downstream files a stable named conclusion so
they do not repeatedly normalize the expanded `metricDerivNormSupOn`
existential.

Verification passed: focused check and targeted module build succeeded.  The
new wrapper is axiom-clean with the expected project axioms only.

## 2026-07-14 post-merge compatibility

The live rebuild exposed that the broad `simp` proof of
`metricDerivNorm_symm` no longer closed the final additive identity. The proof
now unfolds only `metricDiffCovDerivAt` and uses `abel` for the fibrewise
identity `B - A = -(A - B)`. Focused verification passed; the theorem statement
and all geometric inputs are unchanged.
