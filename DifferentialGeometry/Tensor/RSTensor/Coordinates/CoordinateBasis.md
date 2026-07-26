# CoordinateBasis — notes

Pointwise covariant-tensor coordinates from a tangent basis (`component0S`, `tensor0SBasis`,
`basisTensor0S`, `ext0S_basis`), generic over `𝕜`.

## 2026-06-14 — component-eval API hardening (item 4)
Added `component0S_congr_slots` (next to `component0S_apply`): rewrite a covariant component's slot map
under `slots = slots'`, so downstream proofs avoid `backward.isDefEq.respectTransparency false` for slot
manipulation. Trivial (`rw [h]`), additive, focused-check green. See
`Tensor/RSTensor/ComponentEvalApiPlan.md` for the batch + the validation-target mismatch finding.
