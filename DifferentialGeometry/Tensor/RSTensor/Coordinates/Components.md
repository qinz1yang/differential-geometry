# Coordinates/Components — notes

Real-facing mixed component map `componentRS` + `extRS_basis` over the realized Hom model
`TensorRSSpace r s I x`.

## 2026-06-14 — component-eval API hardening (item 4)
Added `componentRS_congr_slots` (next to `componentRS_apply`): Real-layer slot-map rewrite for a mixed
component. Additive (`rw [hu, hl]`), focused-check green. (The generic analogue is
`componentRS_gen_congr_slots` in `Tensor/RSTensor/Components.lean`.) See
`Tensor/RSTensor/ComponentEvalApiPlan.md`.
