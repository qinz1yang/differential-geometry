# KoszulDifference

## 2026-07-12 branch-alignment compatibility

`nabla_metric_two_term` now normalizes tensor subtraction using the project-level
`Tensor0SSpace.add_apply`, `zero_apply`, and `smul_apply`, then uses `neg_injective`. This replaces
coercion-sensitive `simp`/`linarith`. Focused verification and targeted build passed; the two-term
and Koszul-difference theorems remain complete (100%).
