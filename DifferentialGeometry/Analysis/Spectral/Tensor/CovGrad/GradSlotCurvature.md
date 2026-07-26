# GradSlotCurvature

## Role

This module packages the Ricci commutator for the first two slots of a second
covariant gradient as a fixed smooth curvature coefficient.

## Verified state

`gradSlot_sub_eq_curv` is public, sorry-free, and passes focused verification.
It extracts the generic curvature producer previously available only inside
the oversized DeTurck remainder file.

The named module refresh is blocked before reaching this file by the unrelated
shared-tree failure in `Geometry/Operator/Operators.lean`. The local theorem
has no remaining proof goal; downstream import verification must be rerun once
that upstream file is green.

This producer is complete (100%). The consuming import migration is implemented
but not yet fully reverified.
