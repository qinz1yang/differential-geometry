# PushforwardVF status

## Producer bricks

- `Diffeomorph.pushforward_image` exposes the transport-free identity
  `(Φ_* W)(Φ x) = dΦ_x(W_x)`.
- `Diffeomorph.pushforward_refl` specializes this to the identity
  diffeomorphism.  It is the initial-time linear identity required when the
  harmonic-map gauge starts from `id`.
- `Diffeomorph.mfderiv_symm_self` and
  `Diffeomorph.mfderiv_self_symm` export the two derivative cancellation
  identities for a diffeomorphism and its inverse.  Equivalent arguments were
  previously available only as private lemmas in the Ricci naturality files.

These facts were previously reproved as private lemmas in two naturality
files.  Exporting them here gives the gauge construction one canonical API
without changing the definition of `Diffeomorph.pushforward`.

## Verification state

Focused verification of the expanded `PushforwardVF.lean` passed after the
shared exported-artifact restoration, with no local warnings.  In particular,
all four producer bricks above are now accepted Lean theorems rather than
source-only drafts.

## Endpoint accounting

These are algebraic initial/linear bricks only.  Harmonic-map heat-flow
existence and diffeomorphism preservation remain 0%, and the exact theorem
`ricci_flow_forward_unique` remains 0%.
