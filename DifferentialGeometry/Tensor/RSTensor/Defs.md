# RSTensor Defs

## 2026-07-12 — opaque-fiber evaluation API

- Added canonical `Tensor0SSpace` evaluation lemmas for negation, subtraction, finite
  sums, and natural-number scalar multiplication, alongside the existing
  zero/addition/field-scalar lemmas.
- These are representation-boundary projection lemmas, not new tensor concepts or assumptions.
- Focused verification and the targeted upstream refresh passed without `sorry`.
