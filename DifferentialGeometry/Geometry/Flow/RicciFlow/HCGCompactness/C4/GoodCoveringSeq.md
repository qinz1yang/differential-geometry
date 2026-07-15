# GoodCoveringSeq

## 2026-07-01 NetLimitData Refinement

- Added `NetLimitData.subseq` so the diagonal net-limit package can be refined
  along a further strict master subsequence without rebuilding the radius-limit
  data.
- Added simp projections for the refined master subsequence and unchanged
  limit radii, plus `NetLimitData.stable_subseq` to carry pairwise `B`-ball
  intersection stability through a later refinement.
- Verification passed for the focused file check. The first attempt timed out
  after the external command boundary and left a stale Lake lock under the same
  token; the process was gone, the stale Lake lock was released, and the retry
  passed.
- The targeted module refresh also passed. Warnings were replayed from existing
  upstream modules, not from the new `NetLimitData` helpers.

## 2026-07-09 Sequence-Center Separation Producers

- Added `seqCenter_zero`: the zeroth ordered-net center is the pointed basepoint.
- Added `seqCenter_dist_ge`: every nonzero live center is at least `lambda D 0`
  from the basepoint in the realized proper metric.
- Added `seqCenter_edist_ge`: the same lower bound in the stored Riemannian
  emetric, using `ProperMetricOn.realizes`.

These are sequence-native projections of the existing `OrderedNet` facts, and
are the concrete good-covering input for Step B's basepoint-weight
concentration.  Focused verification and the targeted module refresh passed.

## 2026-07-09 Scaled Inner Cover

- Refactored the eventual hat-cover estimate into `NetLimitData.scaled_cover`:
  every fixed factor strictly larger than `2` eventually covers the source
  ball by the corresponding limit-scale balls.
- Kept `hat_cover` as the factor-`4` compatibility wrapper and added
  `inner_cover` at factor `3`.

The factor-`3` cover leaves a strict collar inside the existing factor-`4`
hats.  This avoids strengthening the stable Step-C interfaces to factor `5`
and is the geometric room needed for special bump numerators.  Focused
verification and the targeted module refresh passed.

## 2026-07-10 Live-Center Injectivity Floor

- Added `seqCenter_mu_hasInj`: a live ordered-net center in slot `alpha` has
  injectivity radius at least `mu (2 * lambda D 0 * alpha)`, uniformly in the
  sequence index.
- The proof combines the checked `lbl389` radius window, the realized-distance
  bridge, and `mu_hasInj_of_le`; it does not add a new radius assumption.

This is the correct fixed-slot injectivity half of the Route-A scale producer.
It is not yet the moving inverse-exponential branch scale, and it does not
resolve the current over-quantification over dead slots.  Focused verification
passed.

## 2026-07-13 Pair-intersection symmetry

Added the small canonical lemma `BInter.symm`.  It only swaps the two center
witnesses and uses symmetry of `Disjoint`; it lets the one-way H6 pair-tail
producer be applied in the reverse direction without a duplicate intersection
assumption.  Focused verification passed.  This helper is complete, while the
finite pair-to-Step-C integration remains separate machinery and the target
compactness theorem remains 0%.

Added `NetLimitData.binter_stable_tail`.  On one common finite tail, every
currently intersecting pair in the frozen finite cage belongs to the
eventually-intersecting branch of the stable net.  Together with `BInter.symm`,
this is the exact finite bookkeeping used by `InterSlot`; focused verification
and the targeted refresh passed.
