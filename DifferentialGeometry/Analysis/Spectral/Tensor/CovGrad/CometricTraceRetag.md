# Cometric trace retagging

## 2026-07-13 pointwise producer

`trace_slot_flat` is proved without symmetry assumptions on the rank-two
covariant tensor.  The proof scalarizes the rank-zero output, expands both
cometric traces in local orthonormal frames, evaluates `slotExtendFib` only at
slots, and closes the change of frame by the metric flat/sharp identities and
orthonormal expansions.  It never asks Lean to compare an entire dependent
Hom-bundle value.

Focused verification passed.  There are no `sorry`s or hidden consumer
assumptions in this producer.

The next frontier is field assembly in `ScalarNonautTame.lean`:
`trace_retag_eq`, then `scalar_trace_factor`, then `scalar_flux_split` using the
already verified `covDiv_appCc` identity.

