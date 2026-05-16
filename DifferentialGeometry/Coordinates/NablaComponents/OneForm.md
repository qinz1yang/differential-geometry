# OneForm Nabla Component Notes

## 2026-05-10 scalar genericity

- Worked: generalized the one-form coordinate component, moving-slot, and
  local-frame smoothness route from `Real` to generic `ð•œ`.
- Worked: the one-form file now consumes the generic
  `TensorMultilinear.contMDiffAt_section_apply` and generic
  `extDerivFun_apply_contMDiffAt`.
  and module rebuild through

## 2026-05-11: Smooth one-form component API

- Lowered the one-form coordinate component, moving-slot, and smoothness consumers from analytic/top regularity to smooth regularity.
- The existing product-rule proofs survived after the smooth coordinate derivative bridge was rebuilt.
- Verification passed.
## 2026-05-12: Smooth moving-slot evaluation wrapper

- Added `nabla0SFun_one_eval_smooth_slots`, a public wrapper around the existing
  coordinate moving-slot formula for smooth vector-field slots.
- This is the reusable one-form formula
  `(nabla_X alpha)(Z) = X(alpha Z) - alpha(nabla_X Z)`.

## 2026-05-12: Rank wrapper cleanup

- Replaced the one-form model and coordinate component proofs with direct
  specializations of the generic `(0,s)` component factory in `Basic.lean`.
- Kept the public one-form theorem names as readable wrappers.
- Verification passed.

## 2026-05-13: coordinate-frame evaluation exposed

- Worked: made `oneForm_eval_coordinateFrame_contMDiffAt` public so
  Levi-Civita curvature proofs can reuse the existing one-form coordinate
  smoothness bridge instead of copying it locally.
- Also made `oneForm_pair_coordFrame_eventually` public.  This is the reusable
  local-frame reconstruction step for evaluating a one-form on a moving vector
  field.
- Verification passed.
