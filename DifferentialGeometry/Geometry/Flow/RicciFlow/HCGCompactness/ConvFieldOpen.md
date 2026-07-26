# ConvFieldOpen

## 2026-07-17 open-time diagonal layer

This file is the book-facing time-window layer above the checked fixed-window
`ConvOut` producer.  It fixes one `PointedCGHMaps`, reference metric, and bump
family before any time-window extraction.

`BumpMetricConv` records exactly the existing `ConvOut.conv` and `convPt`
conclusions for an explicit reindexing.  Its subsequence, tail, window
restriction, limit-family congruence, and uniqueness lemmas are the stability
interface required by `exists_diag_subseq`; it is not a new geometric input.

`OpenConvOut` records one subsequence and one limit metric family on all
canonical compact windows.  `exists_openConv` diagonally refines the supplied
fixed-window producers and glues the local metric limits by the checked
compact-open uniqueness theorem.  `conv_Icc` then recovers convergence on an
arbitrary closed interval contained in the open time domain.

The producer-side bridge is now checked.  `BumpMetricConv.of_compSubseq` reads
a fixed-window result for reindexed comparison maps back as convergence of the
original extended sequence along the composed index.  `exists_openConv_raw`
then reruns the existing `convOut` after every prescribed refinement, fixes one
original bump family, diagonally extracts one subsequence, and glues one limit
metric family on all canonical windows.  It does not choose a per-window bump
family or add an endpoint assumption.

Focused verification and the exact module refresh are green.  The remaining
P4 work is above this diagonal layer: produce its four raw window hypotheses
from the theorem-level sequence-flow data uniformly over all canonical
windows, and prove joint spacetime regularity of the glued limit family.

## 2026-07-18 grow-local diagonal propagation

The fixed-window and reindexed `hcovTail` hypotheses are now stated on
`bf.grow k`. Subsequence transport uses the bump-family grow identity
directly and no longer normalizes a source-domain membership proposition.
Focused verification and the exact module refresh pass.
