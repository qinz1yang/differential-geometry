# StepCPartition.lean

## 2026-06-30

Added the first Step-C partition producer layer from the already-proved Step-A
good-covering data.

Implemented:

- `NetLimitData.hatBall`, the finite `γ < A r` hat-ball family at a large
  sequence index `k`, with absent net centers interpreted as empty hats;
- `NetLimitData.hatBall_open`, openness of each hat in the realized proper
  metric;
- `NetLimitData.hatBall_cover`, the eventual finite cover of
  `Metric.closedBall O_k r` by the `Fin (A r)` hats, directly from
  `NetLimitData.hat_cover`;
- `NetLimitData.hatPOU_of_cover`, a smooth partition of unity subordinate to a
  fixed finite hat cover;
- `NetLimitData.hatPOU_eventually`, the eventual smooth partition-of-unity
  producer from the Step-A finite cover;
- `NetLimitData.hatPOU_nonneg`, nonnegativity of each produced weight;
- `NetLimitData.hatPOU_sum_one`, the finite-sum form of the partition identity
  on the covered ball;
- `NetLimitData.hatPOU_pos`, existence of a positive active weight at each
  covered point;
- `NetLimitData.hatPOU_active_mem`, the support-to-hat bridge for nonzero
  weights;
- `NetLimitData.hatPOU_weights`, the bundled weight package needed by the
  center-average consumer.
- `NetLimitData.hatPOU_active_data`, the consumer-shaped pointwise package
  combining normalized weights with the active-support-to-hat bridge.

The earlier topology seam is discharged by `ProperMetricOn.top_eq` in
`GoodCoveringOrdered.lean`: the metric topology induced by `ProperMetricOn.ms`
is the stored manifold topology. The direct no-bridge POU attempt first failed
with the expected instance mismatch (`ProperMetricOn.ms` metric topology versus
the stored manifold topology); `ProperMetricOn.top_eq` is the reusable bridge.

Remaining boundary:

- This file now provides the finite smooth POU layer. The next Step-C boundary is
  consuming these finite weights with the already-proved center-average
  convergence wrappers to build the radius-window averaged maps.

The finite-sum bridge uses Mathlib's `finsum_eq_sum` plus finite support over
`Fin (A r)`; the active-support bridge routes from `support` to `tsupport` and
then through the partition's subordinate-open property.

Verification status: focused Lean check and targeted module build passed; axiom
checks for the new public cover, POU, weight, and active-data lemmas use only
the usual project axioms.

## 2026-07-01, hat subsequence projection

Added `NetLimitData.hatBall_subseq`.

This is the definitional stability lemma for the finite hat family under a
later master-subsequence refinement: the hats for `L.subseq hψ` at index `k`
are exactly the original hats for `L` at index `ψ k`.  This keeps later Step-C
transition refinements from unfolding `hatBall`, `NetLimitData.subseq`, and
`lamInf` by hand.

Verification status: focused Lean check and targeted module refresh passed.

## 2026-07-09 Finite POU and inner-cover layer

Added a direct constructor `pouOfFinite` for a finite family of globally smooth
nonnegative weights whose sum is one on the source.  Added the cutoff-normalized
family `cutoffWeights` and `pouOfCutoff`; its denominator

`tau * sum atoms + (1 - tau)`

remains positive across the zero-denominator boundary, so the global extension
is genuinely smooth rather than an implicit `0 / 0` convention.  The support
of each cutoff weight stays inside the support of its raw atom.

Added the factor-`3` `innerBall` family, subsequence stability, openness,
inclusion in the factor-`4` hats, and the eventual source-ball cover.  These
theorems deliberately preserve the existing factor-`4` Step-C join interface.

Verification passed.  This is producer machinery only: the concrete special
atoms and the final `StepB1RawInput` producer remain open.

## 2026-07-13 active-hat intersection bridge

Added `NetLimitData.binter_of_mem_hat` and `binter_of_active`.  Two finite hats
containing the same point give a current five-lambda `BInter`; a nonzero
subordinate POU weight supplies the second hat membership automatically.
Focused verification and the targeted refresh passed.  These lemmas identify
the positive interacting pairs but do not by themselves resolve the capstone's
whole-cage `hKV` quantifier.
