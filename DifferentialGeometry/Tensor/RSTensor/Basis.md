# Basis — notes

Fixed tensor-bundle trivialization apply lemmas for `(0,s)` / `(r,s)` tensors
(`Tensor0SSpace.constInChart`, `trivializationAt_apply`, `continuousLinearEquivAt_apply`,
`continuousLinearMapAt_apply`, `TensorRSSpace.trivializationAt_apply`, `trivializationAt_basis_coord`).

## 2026-06-14 — `constInChart_apply` added (component-eval API hardening, item 4)
Added `Tensor0SSpace.constInChart_apply` next to `continuousLinearMapAt_apply`:
```
(constInChart s x₀ β x) v = β (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (v i))
```
for `x ∈ baseSet`. Proof = `rw [constInChart, triv_symmL_eq_compContinuousLinearMap, compContinuousLinearMap_apply]`.

Why: this is the missing theorem-form apply lemma for `constInChart`. Downstream proofs were forced to
`rw [Tensor0SSpace.constInChart]` (the raw def-unfold), which only matched under
`set_option backward.isDefEq.respectTransparency false`. With `constInChart_apply`, downstream evaluates
`constInChart` through a clean lemma and drops the hack — it compiles **green without any transparency
option** here (the bundle reasoning never needed it; only the downstream wrapped-term `rw` did). First
consumer: `NablaComponents/TensorRS/ApplyInput.lean` (`constInChart_basisTensor0S_coordFrame`). See
`Tensor/RSTensor/ComponentEvalApiPlan.md`.
