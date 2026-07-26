# StepCAtoms.lean

## 2026-07-09: intrinsic atom family and pointwise weights

This file closes the concrete atom layer between the strict inner cover and the
generic Step-C pointwise weight interface.

Delivered:

- `stepCBump`, with scalar quadratic radii `(3 * lam)^2` and
  `(7 * lam / 2)^2`, together with its projection and outer-radius lemmas;
- `stepCAtom`, the intrinsic `quadNormal` specialization;
- `seqAtom`, which is zero for a dead ordered-net slot and the centered atom for
  a live slot;
- `seqAtom_contMDiff`, proving the whole ordered-net atom family globally
  smooth by separating the zero and quadratic-normal cases;
- `seqAtom_Icc` / `seqAtom_nonneg`;
- `seqAtom_one`, proving that a live atom is one on its strict `3 * lam` inner
  ball;
- `seqAtom_mem_hat`, proving that a nonzero atom lies in its `4 * lam` hat;
- `seqWeights_data`, which turns a supplied per-index inner-ball cover and an
  explicit base slot into `centerAverage.WeightDataOn` via `cutWeights_data`;
- `seqWeights_ev`, which combines `innerBall_cover` with `seqWeights_data` to
  give the same package eventually on `NetLimitData.hatSourceBall`;
- `baseIndex`, the canonical zeroth slot for `r >= 0`.  No new field on
  `PackingBound` is needed: applying its existing cardinal bound to the
  basepoint singleton proves `0 < A(r)`;
- `seqAtom_base` and `seqWeights_base`, proving respectively that the zeroth
  atom is one at the pointed basepoint and that the normalized weights there
  are the Kronecker delta at slot zero;
- `seqWeights_zero_ev`, the eventual source-ball package specialized to that
  canonical slot.

The two realized ball arguments now reuse the public producers
`properBallNormal` and `properExpDist` from `StepCAveragePOU`.  This removes the
duplicated local construction of the Riemannian fibre norm and the repeated
`ProperMetricOn.realizes` conversion while leaving the atom statements and
their radii unchanged.  The producer layer owns that instance-sensitive bridge;
this file only consumes its normal-coordinate vector and distance equality.

The producer-based refactor and the eventual/basepoint additions passed focused
verification without local warnings; the earlier targeted module build passed.
This atom/pointwise-weight sub-brick is complete.  The `StepB1RawInput` producer
and the textbook B1 theorem remain unstated/unproved (0%); their dedicated
machinery is now roughly 58%.
Step-B/B1 machinery is about 58%, Chapter-4 machinery about 64%, and the whole
HCG compactness machinery about 45%; final compactness endpoints remain 0%.

## 2026-07-13 finite-slot scale migration

All pointwise atom and weight lemmas now consume only
`Item3GpScaleAt ... pb r k`. The two eventual weight packages consume
`Item3GpScaleTail` and intersect it with the existing source-ball cover tail.
No atom consumer requires the legacy all-index `Item3GpScaleInput`.

Focused verification and the narrow refresh passed. This consumer migration
is complete; the `StepB1RawInput` producer and textbook B1 remain theorem-level
0%, while their dedicated machinery is about 80%. Chapter 4 machinery is
about 76%, whole-HCG machinery about 53%, and compactness endpoints remain 0%.

## 2026-07-16 subsequence stability

`seqAtom_subseq` records the canonical reindex identity for each actual
finite-stage atom.  Its proof separates the dead/live center cases and uses
proof irrelevance only for the positive-radius witness, so downstream map
definitions no longer unfold `seqAtom` to compare refined stages.

Focused verification passed.  This atom-level adapter is complete; it is
infrastructure for the master radius diagonal.  `StepB1RawInput` and textbook
B1 remain theorem-level 0%; dedicated Step-B/B1 machinery is roughly 98%,
Chapter-4 machinery roughly 90%, and whole-HCG machinery roughly 60%.
