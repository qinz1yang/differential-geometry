# Rank-zero metric inner-product bridges

## 2026-07-10

- Added `inner_nat_cast`, `lower_toRS0`, `inner_toRS0`,
  `inner_toRS0_zero`, and `inner_toRS0_scalar`.
- The lowering proof is performed only after applying the model tensor to its
  multilinear slots.  It never asks Lean to compare whole Hom-bundle model
  objects, avoiding the expensive topology/normalization path seen in
  `nablaRSFun_eval_moving_raw`.
- The general theorem carries the explicit `Fin (0 + s)` transport and then
  removes it through slot-permutation invariance.  This avoids relying on
  numeral-only definitional reductions of `0 + s`.
- No locally constant chart hypothesis or consumer-side realization assumption
  was added.
- Focused verification and targeted module verification passed.
