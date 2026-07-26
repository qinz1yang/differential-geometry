# StepCTransitionRefine.lean

## 2026-07-01, fixed-pair refinement bridge

Added the subsequence-stability bridge needed before the finite Step-C hat
fold can reuse the fixed-pair Step-B transition producer.

Implemented:

- `ExpInverseDerivBoundInput.subseq`: reindexes the `lbl418` exp-inverse
  derivative input along any subsequence.
- `existsTransRefine`: reruns `exists_transitionLimit_normalTransition` after
  an already chosen strict master subsequence and records that the composed
  subsequence remains strict.
- `existsTransFinite`: folds the fixed-pair refinement over a finite family of
  transition pairs, producing one shared strict subsequence and per-pair
  transition limits.
- `existsTransUniv`: specializes the finite extractor to a full finite index
  type and exposes actual endpoint families `Jinf i`, `Jbarinf i`, including
  continuity facts in the shape expected by the decoded-composition averaging
  bridge.

This does not choose finite-hat domains.  It does close the abstract finite
subsequence-alignment part: once the concrete hat layer supplies centers,
domains, overlap containment, and cocycle data for the finite hat index type,
the common transition-limit subsequence and family-valued transition limits are
now produced by `existsTransUniv`.

Verification status: focused Lean check and targeted module build passed.  The
axiom probe for `existsTransRefine`, `existsTransFinite`, and
`existsTransUniv` reports only the usual project axioms.  No new `sorry` or
`admit` occurs in this file.

## 2026-07-08 canonical subseq cleanup

Removed the local duplicate `ExpInverseDerivBoundInput.subseq`; its canonical
home is now `StepBInputs.lean`, where both Step B and later Step C/D consumers
can import it without declaration collisions.  The refinement theorems still
call `ExpInverseDerivBoundInput.subseq`, now resolved through the Step B input
API.

## 2026-07-13 H6 refinement path

Added `existsTransRefH6`. It reindexes `NormalCoordMetricBoundInput` along the
existing strict master subsequence and calls `exists_trans_h6`; the composed
subsequence and both transition limits have the same output shape as the S6
compatibility theorem. Focused verification passed.

`existsTransFinite` and `existsTransUniv` now use this H6 path.  Their canonical
parameters distinguish convergence-domain families `U`, `V` from target-anchor
families `Ua`, `Va`.  The anchors carry openness, boundedness, metric, and
C2-radius containments; the source domains retain their own openness, metric,
and C2-radius containments.  Forward and reverse transition `MapsTo` hypotheses
land in `Va` and `Ua`, respectively, while limit convergence and conditional
cocycle output stay on `U`, `V`.  The finite induction reindexes every anchor
family and containment along the shared subsequence before calling
`existsTransRefH6`; the universal form remains only the `Finset.univ`
specialization and still exports continuity of both limit families.  Focused
verification passed.

After `stepCJoin` migrated to the H6 universal extractor, a live search found no
remaining consumer of `existsTransRefine`.  The obsolete S6 compatibility
theorem was removed and focused verification passed.  The finite/universal H6
migration and the transition-refinement compatibility cleanup in this file are
both 100%.

`NormalTransAt` now packages the pointwise two-way H6 geometry at one sequence
index, with convergence domains separated from bounded target anchors.
`existsTransTail` takes one common tail for a finite eventual family and then
calls `existsTransUniv`; it returns the same forward/reverse limits and
conditional cocycles on a composed strict subsequence.  Focused verification
and the targeted refresh passed.  No S6 compatibility declaration remains in
this file.

## 2026-07-18 framed radius migration

The complete extraction chain now uses `expRadiusGp`: `existsTransRefH6`,
`existsTransFinite`, `existsTransUniv`, and `NormalTransAt`.  This is a direct
signature migration to the already-framed `exists_trans_h6`; the subsequence
and finite-diagonal proofs are unchanged.  Focused verification passed and the
diff is clean.  The exact refresh is intentionally ordered after
`StepCAtomConv` and before `StepCPairTail` so downstream diagnostics read one
coherent interface generation.
