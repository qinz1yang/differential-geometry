import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalUFinalP6M6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CloseLateHICgFinalP6HF

/-!
# `hclosGF_of_HU_final_P6M6` ↔ HCLOSEF `hcloseF_plus_P6HF` 的 `hclosGF` binder：类型对齐检查（`_P6M6`）

`hcloseF_plus_P6HF` 是封闭陈述（`∃ epsW, … ∀ … (hclosGF : …) → … → False`），不能直接做偏应用；
本文件在 elaboration 时沿它的 `∃ / ∧ / ∀` 链进到名为 `hclosGF` 的 binder，取其类型 `d`，
把 `hclosGF_of_HU_final_P6M6` 的前 24 个参数实例化成元变量后，检查**结论 `isDefEq` `d`**，不通过则报错。
不引入任何声明（无 `def` / `theorem`，只有一条 `run_meta`）；依赖 HCLOSEF G1–G4 已在上游。
-/

set_option autoImplicit false

open Lean Meta Elab Command

run_meta do
  let top := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
  let ci1 ← getConstInfo (top ++ `hcloseF_plus_P6HF)
  let ci2 ← getConstInfo (top ++ `hclosGF_of_HU_final_P6M6)
  let ty1 := ci1.type.instantiateLevelParams ci1.levelParams [Level.zero]
  let ty2 := ci2.type.instantiateLevelParams ci2.levelParams [Level.zero]
  -- ∃ epsW, 0 < epsW ∧ ∀ ε …, ∃ C, 1 ≤ C ∧ ∀ … (hclosGF : d) → … → False
  lambdaTelescope ty1.appArg! fun _ b1 =>
  forallTelescope (b1.getArg! 1) fun _ b2 =>
  lambdaTelescope b2.appArg! fun _ b3 =>
  forallTelescope (b3.getArg! 1) fun ws _ => do
    let mut found := false
    for w in ws do
      if (← w.fvarId!.getUserName) == `hclosGF then
        found := true
        let d ← inferType w
        let (_, _, concl) ← forallMetaTelescopeReducing ty2 (some 24)
        unless ← isDefEq concl d do
          throwError "hclosGF_of_HU_final_P6M6 conclusion is NOT defeq to the hclosGF binder"
    unless found do throwError "no binder named hclosGF in hcloseF_plus_P6HF"
