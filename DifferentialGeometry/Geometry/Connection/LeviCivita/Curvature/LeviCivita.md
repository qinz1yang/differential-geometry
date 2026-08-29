# `LeviCivita.lean`

## Smooth-slot tensor derivative evaluation

The existing generic smooth-slot evaluation of `nabla0SFun` for covariant
two-tensors is public as `nabla0S_two_apply`.  The proof and assumptions are
unchanged; only its visibility and short API name changed so pointwise
geometric trace consumers can reuse the established formula rather than
reprove it.

Focused verification passed without warnings or placeholders.
