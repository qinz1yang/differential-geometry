# TotalNabla0SLinear

## 2026-07-12 branch-alignment compatibility

The scalar and additive proofs now use the project-level `Tensor0SSpace.smul_apply` and
`Tensor0SSpace.add_apply` at both tensor evaluation layers. The former Mathlib-level rewrite no
longer matched the realized bundle operations. Focused verification and targeted build passed;
both linearity theorems are complete (100%).
