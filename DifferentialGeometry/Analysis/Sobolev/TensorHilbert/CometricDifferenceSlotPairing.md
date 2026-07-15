# Cometric-difference slot pairing

## 2026-07-14 Green-sign bound

The generic negative-sign producers `negDiffSlot_point_le` and
`neg_gInvDiffSlot_le` now control the slot action of
`-gInvDiffRaisedEndo` by `δ / (1 - δ)`. This is the sign created by Green
integration in the scalar moving-Laplacian principal arm; the older positive
one-sided theorem was insufficient for that use.

The proof reuses self-adjointness, the absolute inverse-cometric perturbation
bound, and the existing generic slot-pairing integrator. It adds no consumer
assumption. Focused verification and the exported producer refresh passed.

This remains supporting machinery. The scalar principal pairing and all
Noncollapsing/conjugate-heat endpoint theorems are accounted separately.

## 2026-07-14 Arbitrary-slot sharp bound

Added `gInvDiffSlotAt`, `negDiffSlotAt_le`, and the integrated
`negSlotAtL2_le`.  The pointwise proof splits the orthonormal component index
at an arbitrary `j : Fin r` with `Equiv.funSplitAt`, then applies the same
one-dimensional self-adjoint quadratic-form estimate used in the leading-slot
case.  Consequently the coefficient stays exactly `δ / (1 - δ)` and is
independent of the tensor rank and chosen slot.

Focused verification passed.  This is reusable arbitrary-slot machinery; it
does not by itself prove the scalar tame estimate or any Noncollapsing endpoint.
