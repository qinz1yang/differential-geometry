# NoncollapseOpen

## 2026-07-23 positive-start half-open interval

Added `noncollapse_after`.  It upgrades the fixed positive regular-slab theorem
to a `[0, omega)` flow interval after any fixed positive start time `a`.  The
proof uses `w_span_uniform` directly with a time-dependent finite auxiliary
upper endpoint `b < omega`, while keeping the W lower constant independent of
the later flow time.

Focused verification and the module artifact refresh both passed.  This does
not prove the all-carrier `NoLocalCollapsing` endpoint: times near the initial
boundary still require the separate `early_ball_low` producer.

## 2026-07-23 initial boundary closed

`FamilySmallBall.family_vol_low` and the `EarlyBall` chain now provide that
initial-boundary producer without a local `sorry`. Consequently
`EarlyBall.no_local_open` is the complete source theorem for all-carrier
`NoLocalCollapsing` on the half-open flow interval. The remaining
axiom-cleanliness issue is upstream in the positive-time entropy route: its
Galerkin classical-slice construction still inherits the Weyl
diagonal-kernel counting `sorry`.

## 2026-07-23 axiom-clean closure

The preceding caveat is now obsolete. The exact scalar Galerkin consumers use
`scalar_eigen_tail`, whose axiom audit is clean, and the strong generic Weyl
theorem has no Entropy/Perelman consumer. The refreshed endpoint artifact
shows `no_local_open` depends only on the standard foundational axioms and not
on `sorryAx`.
