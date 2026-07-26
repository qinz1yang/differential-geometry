# Sharp-flat covector endomorphism field

## 2026-07-13 canonical producer extraction

The smooth field `sharpFlatEndoCc g0 g1`, representing `g0-flat` composed with
`g1-sharp`, now lives below the connection-difference jet tower.  Its existing
public declaration names and section simp theorem were preserved; the old
tower imports this module and continues to use the same API.

Focused verification passed for both the new producer and the downstream
`ConnectionDifferenceJetTower.lean` compatibility check.  The targeted
producer refresh reached its outer wall-clock limit after writing the required
`.olean`; the subsequent downstream focused check was green, so this was a
verification-resource timeout rather than a Lean proof failure.

This extraction is supporting machinery only.  The next mathematical producer
remains the field-level trace factorization in `ScalarNonautTame.lean`; no
Noncollapsing endpoint theorem is completed by this move.

## 2026-07-14 scalar evaluation

`sharpFlatEndo_eval` now exposes the action of `g₀♭ ∘ g₁♯` only after
application to a covector and tangent vector. It reuses the mixed sharp
pairing in the cometric multiplier layer and avoids a whole-Hom equality in
the scalar nonautonomous consumer. Focused verification and the producer
refresh passed.
