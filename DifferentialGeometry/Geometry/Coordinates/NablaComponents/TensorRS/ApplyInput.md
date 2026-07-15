# ApplyInput — notes

Hom-input expansion + scalar product-rule bridges for coordinate-frame mixed tensor components
(`constInChart_basisTensor0S_coordFrame`, `applyInput_coordFrame_eventually`,
`tensorRS_eval_constInChart_coordinateFrame_contMDiffAt`, `coordDeriv0SAt_applyInput_eq_sum`).

## 2026-06-14 — component-eval API validation (item 4): 2 → 1 transparency blocks

**Block 1 REMOVED — `constInChart_basisTensor0S_coordFrame` is now hack-free.**
Old proof did `rw [Tensor0SSpace.constInChart]` (raw def-unfold, needs the hack) + `ext v` +
`simp [basisTensor0S, tensor0SBasis, continuousMultilinearMap_basis, …]` (unfolds the basis-tensor internals).
Rewritten with the component API + the new apply lemma:
```
refine ext0S_basis (coordinateFrameAt_basis x₀ hx) (fun slots => ?_)
rw [basisTensor0S_component, component0S_apply, Tensor0SSpace.constInChart_apply r hxE]
simp only [coordinateFrameAt_basis_continuousLinearMapAt x₀ hx]
rw [← continuousMultilinearMap_basis_repr (Module.finBasis 𝕜 E) r, Module.Basis.repr_self, Finsupp.single_apply]
```
RHS via `basisTensor0S_component` (Kronecker, no `basisTensor0S` unfold); LHS via `component0S_apply` →
`constInChart_apply` (NEW, `RSTensor/Basis.lean`) → `coordinateFrameAt_basis_continuousLinearMapAt` (private
here) → model-basis Kronecker. Focused-check **green**. (`constInChart_apply` is the one tiny missing apply
lemma; added at its home layer `RSTensor/Basis.lean`, see `Basis.md`.)

**Block 2 KEPT (stop condition) — `tensorRS_eval_constInChart_coordinateFrame_contMDiffAt`.**
This is a **smoothness** theorem (`ContMDiffAt` of the bundle evaluation) built from `tensorRS_eval_contMDiffAt`
+ `tensor0SConstInChart_contMDiffAt` + `T.contMDiff`; it never uses `component0S`/`componentRS`/`basisTensor0S`.
Empirically removing its hack fails with **`synthInstanceFailed`** at the `TensorRSModel r s 𝕜 E` /
`Tensor0SModel r 𝕜 E` bundle `TotalSpace` / `ContMDiffAt` instance sites (lines ~200/206/208) — the SAME
bundle-topology / `toModel` instance-synthesis family as `Tensor0S.lean`, **not** component-eval. Per the task
stop condition, kept the hack and did not force it. It belongs to the separate bundle-topology workstream.

**Recount: 2 → 1** transparency block remaining (the bundle smoothness one).
