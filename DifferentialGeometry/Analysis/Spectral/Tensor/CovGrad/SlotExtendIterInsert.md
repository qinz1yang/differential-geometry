# SlotExtendIterInsert

## Purpose

`slotExtIter_apply` identifies the `w`-fold passenger extension of a leading-slot endomorphism
insertion with insertion in slot `w`.  This is the natural-slot bridge needed by balanced scalar
commutator pairings: covariant gradients add leading passenger slots while the original coefficient
continues to act on the oldest derivative slot.

`app_slotExt_apply` is the fully applied `appCcRS` consumer bridge.  It evaluates at the base point and
rank-zero input before reducing the operator action to `slotExtIter_apply`.

## Proof route

The proof is by induction on `w`.  At a successor step both sides are fully evaluated on a tuple and
`slotExtendFib_apply_eval` removes the new leading passenger slot.  The remaining scalar equality is
the induction hypothesis.  No whole-Hom equality, chart-local hypothesis, or new consumer assumption
is introduced.

## Verification

Focused verification passed after refreshing the direct imported module.  The successor proof uses
an explicit natural-number rank normal form before applying `slotInsertEndoFib_succ`; this avoids
rewrite matching through differently parenthesized additions.  The fully applied `appCcRS` consumer
bridge also passes focused verification.
