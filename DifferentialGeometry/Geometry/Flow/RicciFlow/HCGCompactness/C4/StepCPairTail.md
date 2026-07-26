# StepCPairTail.lean

## 2026-07-13: live-pair H6 tail

`pair_exp_maps_tail` derives the eventual proper-ball exponential image for one
stabilized live pair from the H6 radius and coercivity profiles.

`pair_overlap_tail` now returns the complete one-way H6 data on that same tail:
the small source ball and large target-anchor ball lie in their respective
`NormalCoordMetricBoundInput.radius` and `expMapC2Radius` balls, the transition
is `C∞` on the source, the normal overlap holds, and the transition maps into
the target anchor.  The last conclusion calls
`StepBTransitionOverlap.normalTrans_mapsTo` directly; no synonymous wrapper was
introduced.  `NormalRadiusProfile.metricScaleTail` supplies the previously
missing metric-control-radius containment.

Focused verification passed.  The one-way fixed-pair tail producer is 100%.
The remaining pair-to-finite integration is about 45%: the reverse direction is
obtained by swapping the live pair once the intersection witness is transported,
but a finite common shift and the actual transition-pair indexing still have to
be threaded into the high Step-C join.  Step-B/B1 dedicated machinery remains
about 83%, Chapter 4 machinery about 79%, and whole HCG machinery about 53%.
`StepB1RawInput`, the textbook B1 theorem, and the conditional compactness
endpoint remain theorem-level 0%.

## 2026-07-13 finite interacting pairs and active support

`exists_pair_trans` now applies the canonical eventual finite extractor in both
directions to any finite family of stably intersecting live pairs.  It returns
one common strict subsequence, forward and reverse C-infinity limits, and the
conditional cocycles.  `InterSlot` is the finite subtype of targets stably
intersecting one fixed live source, and `inter_slot_of_binter` constructs such a
target from one stabilized current intersection plus its eventual branch.

`atom_trans_small` and `weight_trans_small` prove the missing honest active
image estimate.  A nonzero atom, or the corresponding normalized weight, puts
the transition coordinate in the target six-lambda ball, hence inside the
reverse eight-lambda domain.  The proof uses the H6 origin coercivity floor,
`properBall_to_exp`, and `normalTrans_mapsTo`; it adds no endpoint radius input.
Focused verification passed for all declarations.

The remaining capstone blocker is not a pair-tail estimate.  The current
`stepCJoin`/`hatPtsCasesComp` interface asks for `hKV0` on the whole canonical
cage and at every stage, while the checked geometry supplies it only on actual
atom/weight support.  Pair H6 maps the whole source ball only into a larger
item-3 anchor, and its limit cocycle is conditional on already being in the
reverse small domain.  A Euclidean translation with center separation `9` and
unit lambda shows that the all-cage implication is false.  The next design
choice is therefore support-local capstone specialization versus a genuinely
stronger later-reference cage; do not try to derive the old `hKV0` from
cancellation alone.

Finite positive-pair extraction is 100%; the sparse active-support machinery is
about 80%, and pair-to-capstone integration is about 65%.  Dedicated Step-B/B1
machinery is about 84%, Chapter 4 machinery about 80%, and whole HCG machinery
about 53%.  `StepB1RawInput`, textbook B1, and all compactness endpoints remain
theorem-level 0%.

## 2026-07-18 framed migration status

The live source uses `framedExpDiffeo`, `framedExpMap`, and `expRadiusGp`
through the atom, proper-ball, pair-image, and overlap paths; the obsolete
coercivity/square-root conversion was removed. The ordered exact refresh
`StepCAtomConv -> StepCTransitionRefine -> StepCPairTail` completed green, so
this framed pair-tail layer is revalidated. This does not complete
`StepB1RawInput` or the textbook B1 theorem; both remain theorem-level 0%.
