import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaFinalP6M6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CloseLateHICgFinalP6HF

/-!
# `hκRF_of_seedWindow_center_P6M6` ↔ HCLOSEF `hcloseF_plus_P6HF` 的 `hκRF` binder：类型对齐检查（`_P6M6`）

同 `P6HscalUFinalAlignP6M6` 的做法：沿 `hcloseF_plus_P6HF` 的 `∃ / ∧ / ∀` 链进到名为 `hκRF` 的 binder，
取其类型 `d`，把 `hκRF_of_seedWindow_center_P6M6` 的前 21 个参数元变量化，检查**结论 `isDefEq` `d`**，
不通过即报错。不引入任何声明。依赖 HCLOSEF G1–G4 已在上游。
-/

set_option autoImplicit false

open Lean Meta Elab Command

run_meta do
  let top := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
  let ci1 ← getConstInfo (top ++ `hcloseF_plus_P6HF)
  let ci2 ← getConstInfo `GC.LongTime.Ch11.hκRF_of_seedWindow_center_P6M6
  let ty1 := ci1.type.instantiateLevelParams ci1.levelParams [Level.zero]
  let ty2 := ci2.type.instantiateLevelParams ci2.levelParams [Level.zero]
  lambdaTelescope ty1.appArg! fun _ b1 =>
  forallTelescope (b1.getArg! 1) fun _ b2 =>
  lambdaTelescope b2.appArg! fun _ b3 =>
  forallTelescope (b3.getArg! 1) fun ws _ => do
    let mut found := false
    for w in ws do
      if (← w.fvarId!.getUserName) == `hκRF then
        found := true
        let d ← inferType w
        let (_, _, concl) ← forallMetaTelescopeReducing ty2 (some 21)
        unless ← isDefEq concl d do
          throwError "hκRF_of_seedWindow_center_P6M6 conclusion is NOT defeq to the hκRF binder"
    unless found do throwError "no binder named hκRF in hcloseF_plus_P6HF"
