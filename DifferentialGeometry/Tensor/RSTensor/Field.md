# Field

## 2026-05-14 mixed tensor input evaluation

Worked:

- Added `tensorRSField_applyInput_fun` and `tensorRSField_applyInput`, the
  bundled operation evaluating a smooth `(r,s)` tensor field on a smooth
  covariant `(0,r)` tensor field.
- Added `tensor0SModelAt_applyInput_eq`, the fixed-trivialization model
  identity proving that this pointwise evaluation is represented by model-level
  continuous-linear-map application.
- Verification passed.

Failed:

- No mathematical obstruction appeared.  The only local issue was orienting the
  tensor-bundle trivialization inverse with `symmL_continuousLinearMapAt`.

Next step:

- Prove the coordinate derivative Leibniz rule for the component functions of
  `tensorRSField_applyInput`.  Expected hardness: medium tensor-bundle and
  local-frame API work, likely solvable without user intervention.
