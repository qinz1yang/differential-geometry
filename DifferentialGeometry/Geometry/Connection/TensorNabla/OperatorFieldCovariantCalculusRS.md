# Operator-field covariant calculus at generic valence

## 2026-07-13 application associativity

`appCc_assoc` exposes the fibrewise associativity that was previously available
only as a private rank-specialized DeTurck helper.  Its statement keeps the
passenger tensor at contravariant rank zero while allowing the intermediate
operator field to have arbitrary valence.  This is the exact lower-layer bridge
needed to rewrite a traced covariant product rule without unfolding tensor
representations.

Focused verification passed.  The proof is section extensionality followed by
`ContinuousLinearMap.comp_assoc`; it adds no hypotheses and has no analytic
content.

## 2026-07-13 subtraction in the contracted factor

`appCcRS_sub_right` is now public in the generic-valence operator-field layer.
It derives subtraction from the existing additive and homogeneous laws, rather
than repeating a consumer-local Hom extensionality proof.  Full focused
verification and the precise module refresh passed.
