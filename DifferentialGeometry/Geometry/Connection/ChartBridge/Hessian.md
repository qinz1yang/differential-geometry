# Hessian chart bridge

## Current state

- `hessFun_eq_abstract` combines the already proved chart-matrix identity with
  its unconditional global-smoothness producer, so a globally smooth scalar's
  chart Hessian agrees pointwise with `abstractHessian`.
- `hessFun_eq_cov_grad` composes that equality with the existing
  Levi-Civita/gradient identity and the definitional gradient compatibility.
- `hessFun_congr` proves that `hessFun` depends only on the scalar germ at the
  basepoint.
- `hessFun_eq_cov_local` globalizes a scalar germ on an open neighborhood and
  gives the same Levi-Civita/gradient identity from local smoothness alone.
- Focused verification passed.  No new matrix-identity assumption, radius
  assumption, or endpoint field was introduced.

## Next HCG specialization

The scalar-germ localization work is complete and focused-green.  The next
producer is the branch-native `lbl412` specialization in `NormalBranchMin`:
apply `hessFun_eq_cov_local` to `halfSq_inf`, then use `grad_half_inv` as an
eventual equality on the explicit half-cage and the existing covariant-
derivative germ congruence.  This remains a local API assembly, not a new
radius or endpoint assumption.

## HCG accounting

The generic global and local bridge bricks are complete.  The HCG `lbl412`
specialization, the independent `lbl413` positivity/`StrictDistInput`
producer, and `CmHessianInput` remain theorem-level 0% until their named Lean
statements are proved.
