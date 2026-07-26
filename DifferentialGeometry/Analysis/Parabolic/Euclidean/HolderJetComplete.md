# HolderJetComplete

## Status

Source-written only. The shared named build still owns verification, so this
file has not been elaborated by Lean yet.

## Complete contraction topology

The actual topology is now explicit. For each member of a finite
chart/component family, `ParHolderJet` stores bounded continuous spatial jets
of orders `0`, `1`, and `2` on the closed slab `[0, tau] x V`.
`FinHolderJet` is their finite product. Its metric is the inherited product
sup-norm metric, and its ambient space is complete when the target fibre is
complete.

`FinHolderSet` imposes three closed conditions:

- a product sup-norm radius bound;
- a uniform spatial exponent-`1/2` bound on the second jet;
- a uniform temporal exponent-`1/4` bound on the second jet.

`finHolder_closed` proves these conditions are sequentially closed by passing
each Holder inequality through pointwise evaluation limits. Consequently
`finHolder_complete` returns a theorem-valued `CompleteSpace` structure for
the subtype. A fixed-point consumer can install it locally; no global instance
is declared.

Theorems `holderBall_space` and `holderBall_time` state exactly how the limit
retains second-derivative Holder control. Therefore the old extended gauge in
`HolderPath.lean` is no longer being treated as if it were a complete carrier.

## Derivative compatibility

The complete ambient space intentionally stores independent jets. A concrete
Duhamel map must prove that every output realizes the genuine iterated
Frechet derivatives of its component path. `fixed_jet_realizes` then transfers
that realization to a fixed point from the fixed-point equality. This avoids
adding an unproved closed-derivative-graph assumption to the state space.

## Exact next producer

Lift the fixed fine-atlas localized heat/Duhamel operator to a self-map of
`FinHolderBall`, prove its product sup-norm contraction estimate with constants
depending only on the fixed finite cover/cutoffs and uniform coefficient
bounds, and prove its outputs satisfy `FinJetRealizes`.

## Honest progress

- Complete finite parabolic Holder jet carrier: 100% source-written, 0% Lean
  verified.
- Concrete projected Duhamel self-map/contraction: 0% exact theorem.
- Exact `ricci_flow_unif_existence`: 0%.
