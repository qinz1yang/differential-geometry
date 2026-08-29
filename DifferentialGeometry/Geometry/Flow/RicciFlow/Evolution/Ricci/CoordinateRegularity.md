# `CoordinateRegularity.lean`

## Backward-time adapters

`coordGammaBack` composes the existing forward Christoffel evolution theorem
with `s -> T - s`.  `coordConnBack` does the same for the lowered
coordinate-frame connection difference.  Both keep the native coordinate
frame, slot order, and Ricci-covariant-derivative conventions; they do not add a
second connection-variation representation.

These are producer-level coordinate identities used to prove the intrinsic,
fully paired/vector statements in `ConnectionBackward.lean`.  Downstream
L-geometry code does not unfold them or compare whole connection objects.

## Verification

Focused verification passed.  The backward sign is supplied solely by the
time reversal derivative, and there is no remaining local blocker.
