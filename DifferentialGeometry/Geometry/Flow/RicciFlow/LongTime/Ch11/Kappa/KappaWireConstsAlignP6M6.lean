import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaWireConstsP6M6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV6FwdC11GT6

/-!
# `pre841Data_of_certifiedTower_fwd_gap2_P6M6` ↔ GAPTOP6 `…_fwd_C11GT6`（`_P6M6`）

类型对齐检查：两个定理的类型在公共前缀（`pB Γ P g Cdist εReserve T hcert F hF`）之后、`∃ N` 之内，
除 GAP-2 前提（GT6：`N.params.modelAccuracy ≤ epsilon0_C11FR N.epsilon N.C1 N.C2 P` 在 `∃ N` 内部；
本块：N 无关的 `hacc₀` 在 `∃ N` 之外）以外逐字 `isDefEq`。不引入任何声明。
依赖 GAPTOP6 G2′（`A12GapTopV6FwdC11GT6`，未登记）。
-/

set_option autoImplicit false

open Lean Meta Elab Command

run_meta do
  let top := `GC.LongTime.Ch11
  let c1 ← getConstInfo (top ++ `pre841Data_of_certifiedTower_fwd_C11GT6)
  let c2 ← getConstInfo (top ++ `pre841Data_of_certifiedTower_fwd_gap2_P6M6)
  let t1 := c1.type.instantiateLevelParams c1.levelParams [Level.zero]
  let t2 := c2.type.instantiateLevelParams c2.levelParams [Level.zero]
  -- 公共前缀 10 个 binder：{pB Γ P g Cdist εReserve} T hcert F hF；本块再多一个 hacc₀
  forallBoundedTelescope t1 (some 10) fun xs b1 => do
  let t2' ← instantiateForall t2 xs
  forallBoundedTelescope t2' (some 1) fun _ b2 => do
  -- ∃ N, hdiag ∧ rest
  lambdaTelescope b1.appArg! fun ns e1 => do
  lambdaTelescope b2.appArg! fun ms e2 => do
    let e2 := e2.replaceFVars ms ns
    unless ← isDefEq (e1.getArg! 0) (e2.getArg! 0) do throwError "hdiag part differs"
    forallBoundedTelescope (e1.getArg! 1) (some 5) fun ys r1 => do
    forallBoundedTelescope (e2.getArg! 1) (some 4) fun zs r2 => do
      for i in [0:4] do
        let zt := (← inferType zs[i]!).replaceFVars (zs.extract 0 i) (ys.extract 0 i)
        unless ← isDefEq (← inferType ys[i]!) zt do
          throwError "binder {i} differs"
      let r2 := r2.replaceFVars zs (ys.extract 0 4)
      unless ← isDefEq r1 r2 do throwError "conclusion differs"
