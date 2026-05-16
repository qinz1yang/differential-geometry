# TwoTensor Nabla Component Notes

## 2026-05-10 scalar genericity

- Worked: generalized the `(0,2)` coordinate component formulas and arbitrary
  slot expansion from `Real` to generic `ð•œ`.
- Failed: no new proof obstruction appeared after the lower coordinate and
  tensor component layers were made scalar-generic.
  and module rebuild through

## 2026-05-11 symmetry preservation

- Worked: added the general `(0,2)` fact that pointwise symmetry is preserved
  by `nabla0SFun 2`.  The proof is coordinate-based: expand with
  `nabla0SFun_two_eval_coordFrame`, use equality of symmetric component
  functions for the derivative term, and rewrite the two Christoffel correction
  sums by symmetry.
- Failed: no mathematical obstruction in this layer.
- Lesson: the general symmetry-preservation calculation belongs here, not in a
  Levi-Civita/Hessian-specific file.

## 2026-05-11: Smooth two-tensor component API

- Lowered the `(0,2)` component formulas and `nabla0SFun_two_symm_of_symm` from analytic/top regularity to smooth regularity.
- This removes the previous analytic mismatch for LC Hessian consumers. The remaining LC Hessian frontier is first-slot pointwise realization, not this coordinate theorem.
- Verification passed.

## 2026-05-12: Rank wrapper cleanup

- Replaced the `(0,2)` model and coordinate component proofs with direct
  specializations of the generic `(0,s)` component factory in `Basic.lean`.
- The rank-specific file now only performs the small `Fin 2` slot and
  subtraction normalization needed for readable two-index statements.
- Verification passed.
