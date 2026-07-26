# ConstantRicci

## Role

This module contracts the invariant constant-curvature operator identity to
the exact formula

`Ric = (dim - 1) c g`.

It then packages the same equality as the `RicciBoundedBelow` input consumed by
Bonnet--Myers.  This lets the positive Killing--Hopf route obtain compactness of
the normalized universal cover and finiteness of the deck group without the
older `chartRiemannBasisIdentity` assumptions.

## Route

`ricci_of_op` evaluates Ricci in a smooth orthonormal frame, substitutes the
curvature-operator formula, and closes the contraction by the existing
orthonormal Parseval identity.  `ricci_of_rm` and `ricci_of_sec` are the two
geometric entry points; `ricciBound_of_sec` is the Bonnet--Myers adapter.

No coordinate frame or new consumer assumption is introduced.

## Status

Focused verification is GREEN with no warnings.  The file is `sorry`-free.

## Progress accounting

- `ham3_space_box` endpoint theorem: 0%.
- Constant-curvature-to-Ricci producer: 100%.
- Dedicated positive Killing--Hopf machinery overall: approximately 18%.
