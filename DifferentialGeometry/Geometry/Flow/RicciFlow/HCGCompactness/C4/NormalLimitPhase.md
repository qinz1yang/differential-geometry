# NormalLimitPhase

## 2026-07-18 framed-radius migration

`limit_accel_bounds` now proves the phase-domain inclusion from the canonical
`expRadiusGp` positivity theorem.  This matches the already-migrated
`phaseRadius_exp` field and removes the remaining stale `expMapC2Radius`
positivity use from the limit-phase path.

Focused verification and the targeted module refresh passed.  This is a
consumer migration only: it does not construct the sequence-uniform H6 radius
profile or the all-order H6 producer.
