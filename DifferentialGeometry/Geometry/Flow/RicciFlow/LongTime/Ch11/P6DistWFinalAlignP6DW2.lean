import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistWFinalP6DW2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedConditionalP6CD

/-!
# `hdistW_of_firstExit_final_P6DW2` ↔ 条件化 closed 主形的 `hdistW` binder：类型对齐检查（`_P6DW2`）

`false_of_selection_eventSlab_late_closed_cond_P6CD`（`P6ClosedConditionalP6CD:122–137` 的 `hdistW`
binder 所在的封闭陈述）不能直接做偏应用；本文件在 elaboration 时沿它的 `∃ / ∧ / ∀` 链进到名为
`hdistW` 的 binder，取其类型 `d`，把 `hdistW_of_firstExit_final_P6DW2` 的前 25 个参数实例化成元变量后，
检查**结论 `isDefEq` `d`**，不通过则报错（槽形冻结的 Lean 级校验）。不引入任何声明（无 `def` /
`theorem`，只有一条 `run_meta`）。
-/

set_option autoImplicit false

open Lean Meta Elab Command

run_meta do
  let top := `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
  let ci1 ← getConstInfo (top ++ `false_of_selection_eventSlab_late_closed_cond_P6CD)
  let ci2 ← getConstInfo (top ++ `hdistW_of_firstExit_final_P6DW2)
  let ty1 := ci1.type.instantiateLevelParams ci1.levelParams [Level.zero]
  let ty2 := ci2.type.instantiateLevelParams ci2.levelParams [Level.zero]
  -- ∃ epsW, 0 < epsW ∧ ∀ ε …, ∃ C, 1 ≤ C ∧ ∀ … (hdistW : d) → … → False
  lambdaTelescope ty1.appArg! fun _ b1 =>
  forallTelescope (b1.getArg! 1) fun _ b2 =>
  lambdaTelescope b2.appArg! fun _ b3 =>
  forallTelescope (b3.getArg! 1) fun ws _ => do
    let mut found := false
    for w in ws do
      if (← w.fvarId!.getUserName) == `hdistW then
        found := true
        let d ← inferType w
        let (_, _, concl) ← forallMetaTelescopeReducing ty2 (some 25)
        unless ← isDefEq concl d do
          throwError "hdistW_of_firstExit_final_P6DW2 conclusion is NOT defeq to the hdistW binder"
    unless found do throwError "no binder named hdistW in false_of_selection_..._cond_P6CD"
