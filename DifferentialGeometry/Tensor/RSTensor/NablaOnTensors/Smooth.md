# Smooth bundled Nabla wrappers

## 2026-05-11

Added:

- `nabla0S_smooth`, the bundled covariant derivative of a smooth `(0,s)`
  tensor field using `nabla0S_reg`.
- `nablaRS_smooth`, the bundled covariant derivative of a smooth mixed
  `(r,s)` tensor field using `nablaRS_reg`.
- Simp lemmas reducing both wrappers pointwise to `nabla0SFun` and
  `nablaRSFun`.

Verified:

- Verification result recorded without command details.
- Verification result recorded without command details.
Remaining:

- These wrappers are ready for downstream coordinate and Ricci-flow component
  APIs. The mixed coordinate formula itself is blocked on the RS Christoffel
  model-basis identity recorded in `Model.md`.
