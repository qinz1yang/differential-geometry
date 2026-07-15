# Components (generic) — notes

Generic-`𝕜` covariant/mixed component maps: `component0S_product`, `componentRS_gen`,
`componentRS_apply_input_eq_sum`, `extRS_basis_gen`.

## 2026-07-12 — opaque-fiber component projections

- Added generic component lemmas for negation, subtraction, and natural-number scalar multiplication.
- The natural-number case is intentionally distinct from field scalar multiplication; this distinction simplified the dimension-three reaction proof.
- Focused verification and the targeted upstream refresh passed without `sorry`.

## 2026-06-14 — component-eval API hardening (item 4)
Added `componentRS_gen_congr_slots` (next to `componentRS_apply_gen`): rewrite the upper/lower slot maps
of a generic mixed component under `upper = upper'`, `lower = lower'`. Additive (`rw [hu, hl]`),
focused-check green. This is the `_gen` layer used by `coordComponentRSAt`. See
`Tensor/RSTensor/ComponentEvalApiPlan.md`.
