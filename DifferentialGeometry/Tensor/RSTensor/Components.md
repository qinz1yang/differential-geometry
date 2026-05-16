# Components notes

## 2026-05-10 warning cleanup

- Worked: disabled the `unusedFintypeInType` and `unusedDecidableInType`
  linters for this file, preserving uniform component theorem contexts.
- Failed: no proof obstruction appeared.
- Remaining risk: this intentionally avoids public theorem-signature churn.

## 2026-05-10 scalar genericity

- Worked: generalized `component0S_*`, `componentRS`, and `extRS_basis` from
  `Real` to generic `ð•œ`.
- Failed: the first check still saw Real-specialized `component0S` from a stale
  `CoordinateBasis.olean`. Rebuilding `DifferentialGeometry.Tensor.RSTensor.CoordinateBasis`
  made the generic declarations visible and the file then checked.

## 2026-05-14 mixed input expansion

- Worked: exposed the Hom-input expansion as the public theorem
  `componentRS_apply_input_eq_sum`.  It says that evaluating an `(r,s)` tensor
  on a `(0,r)` input and reading a lower component is the finite contraction of
  the input components against the mixed tensor components.
- Verification passed.
- Next step: use this theorem as the pointwise component bridge for the mixed
  Ricci-identity upper-slot contraction product rule.
