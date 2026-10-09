import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.TimeDerivativeMaintenanceC11W3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesFromAstraC11P2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDiagonalDerivative

set_option autoImplicit false

/-!
# S-CH11-W1L4 (G1)：S11 activation 分支 adapter（`_C11W4`，rev2 §5.2）

outer 的 `Inv_C11W` 里 `timeDerivative` 的阈值是当前半径 `(r_{j+1})⁻²`；而 narrow tuple / enhanced
的 S11（`TimeDerivativeSupply_C11E F ρ Ctime`）要的阈值是**对角** `ρ = q.neckRadius`：
`ρ` 在 activation `(5/6)·3^j` 之前沿用旧半径 `r_j`（`PreparedSpatialSuccessor.radius_before_activation`），
之后才是新半径 `r_{j+1}`（`radius_after_activation`）。旧阈值更低，不能用 `Inv` 的新阈值代替。

* `derivative_bound_old_threshold_of_retention_C11W4`（activation 前一支）：`Y` 的**每个** stage
  （`k ≥ X.offset` 用 `derivative_bound_on_old_native_tail`，`k < X.offset` 用 W1L3 的
  `derivative_bound_on_prefix_C11W3`），阈值是旧的 `(X.radius²)⁻¹`，常数仍是 `C.Ctime`；
* `timeDerivativeControl_of_old_threshold_C11W4`（后一支）：旧阈值版 ⇒ `Inv` 的新阈值版
  （`radius_le`），即 W1L3 `timeDerivativeControl_of_retention_C11W3` 的另一证法；
* `diagonal_neckRadius_of_prefix_C11W4`：narrow tuple 的 `hpref`（`q.neckRadius t =
  (S.observation n).parameters.neckRadius t`，`t ∈ [0, n]`）⇒ astra `hdiagonal`；
* `timeDerivativeSupply_of_blockTower_C11W4`（**S11 的 outer producer**）：`BlockTower_C11W` 的
  `toChain` 上，逐块 `retention`（`PhysicalExtension_C11W.retention`）+ `shift_eq` / `offset_eq` 喂
  astra `PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold`
  （`SH/PreparedSpatialDiagonalDerivative`，FIX9 G5 已落地）得对角 `hdiag`，再经 ENHSUP 的
  `timeDerivativeSupply_of_diagonal_C11P2` 得 `TimeDerivativeSupply_C11E F q.neckRadius C.Ctime`。
  activation 的两支在 astra 证明里按几何带 `b_m ≤ v < 3^m` 统一处理（`ρ v ≤ r_m`，`antitone`
  + `radius_after`），不需要对每个 `t` 单独分支；上两条引理给出逐块的分支形。
* consumer：narrow tuple（`exists_surgery_with_spatial_control_and_decay`）的输出 + `BlockTower`
  ⇒ 同一个 `(F, q)` 上的 S11（对应 `a12Enhanced_of_chain_C11P2` 的 `hext` 里 `TimeDerivativeSupply_C11E`
  一项，其 `ρ = q.neckRadius`、`Ctime = C.Ctime`）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **activation 前一支（旧阈值）**：`X` 满足 `TimeDerivativeControl_C11W`，`Y` 是 `X` 的
`PreparedSpatialSuccessor` 并带 retention ⇒ `Y` 的每个 stage 在**旧阈值** `(X.radius²)⁻¹` 之上都有
`C.Ctime` 导数界（`k ≥ X.offset`：old native tail；`k < X.offset`：prefix 运输）。 -/
theorem derivative_bound_old_threshold_of_retention_C11W4 {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {Y : BlockState_C11W pBase C P g (j + 1)}
    {activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    (hX : TimeDerivativeControl_C11W X)
    (hsucc : PreparedSpatialSuccessor X Y activation eta d)
    (hshift : Y.shift = X.history.time (Fin.last X.history.eventCount))
    (hoffset : Y.offset = X.history.eventCount)
    (W : PreparedSpatialStepRetention X Y d eta εcut Dcut mcut)
    (k : Fin (Y.history.eventCount + 1)) (y : (Y.history.stage k).Carrier) (s : ℝ)
    (hs : s ∈ Ioo (Y.history.time k) (Y.history.toHistory.stageEndTime k))
    (hscalar : (X.radius ^ 2)⁻¹ <
      metricScalarAt (Y.history.toHistory.stageMetric k s) y) :
    |derivWithin (fun v => metricScalarAt (Y.history.toHistory.stageMetric k v) y)
      (Iic s) s| ≤
      C.Ctime * metricScalarAt (Y.history.toHistory.stageMetric k s) y ^ 2 := by
  by_cases hk : X.offset ≤ k.val
  · exact W.derivative_bound_on_old_native_tail hsucc hshift hoffset k hk y s hs hscalar
  · exact derivative_bound_on_prefix_C11W3 hX hsucc k (Nat.lt_of_not_le hk) y s hs hscalar

/-- **activation 后一支（新阈值）**：旧阈值版 ⇒ `Inv_C11W` 的 `timeDerivative`（阈值
`(Y.radius²)⁻¹ ≥ (X.radius²)⁻¹`，`radius_le`）；与 W1L3 `timeDerivativeControl_of_retention_C11W3`
同结论（另一证法，同一 `C.Ctime`）。 -/
theorem timeDerivativeControl_of_old_threshold_C11W4 {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {Y : BlockState_C11W pBase C P g (j + 1)}
    {activation eta d εcut Dcut : ℝ} {mcut : ℕ}
    (hX : TimeDerivativeControl_C11W X)
    (hsucc : PreparedSpatialSuccessor X Y activation eta d)
    (hshift : Y.shift = X.history.time (Fin.last X.history.eventCount))
    (hoffset : Y.offset = X.history.eventCount)
    (W : PreparedSpatialStepRetention X Y d eta εcut Dcut mcut) :
    TimeDerivativeControl_C11W Y := by
  intro k y s hs hscalar
  have hr : (X.radius ^ 2)⁻¹ ≤ (Y.radius ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos Y.radius_pos 2) (pow_le_pow_left₀ Y.radius_pos.le hsucc.radius_le 2)
  exact derivative_bound_old_threshold_of_retention_C11W4 hX hsucc hshift hoffset W k y s hs
    (hr.trans_lt hscalar)

/-- narrow tuple 的 `hpref`（对角参数在 `[0, n]` 上等于第 `n` 个观测的参数）⇒ astra 的
`hdiagonal`（`q.neckRadius` 等于对角 `neckRadius`，`v ≥ 0`）。 -/
theorem diagonal_neckRadius_of_prefix_C11W4 (S : PreparedSpatialChain pBase C P g)
    (q : CutoffParameters)
    (hpref : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (S.observation n).parameters.neckRadius t) :
    ∀ v : ℝ, 0 ≤ v → q.neckRadius v =
      (CutoffParameters.diagonal (fun m => (S.observation m).parameters)).neckRadius v :=
  fun v hv => hpref (Nat.ceil v) v ⟨hv, Nat.le_ceil v⟩

/-- **S11 的 outer producer**：`BlockTower_C11W` 的 `toChain` 上，narrow tuple 的 `(F, q)`
（`F.tower = T.toChain.tower`、`q.neckRadius` antitone、`hpref`）满足
`TimeDerivativeSupply_C11E F q.neckRadius C.Ctime`；常数仍是 Γ 的 `C.Ctime`，没有逐块 `C_{time,j}`。 -/
theorem timeDerivativeSupply_of_blockTower_C11W4 {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
    (F : GC.Interface.RawSurgery P g) (hTower : F.tower = T.toChain.tower)
    (q : CutoffParameters) (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hpref : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ),
      q.neckRadius t = (T.toChain.observation n).parameters.neckRadius t) :
    TimeDerivativeSupply_C11E F q.neckRadius C.Ctime :=
  timeDerivativeSupply_of_diagonal_C11P2 F q.neckRadius C.Ctime
    (PreparedSpatialChain.scalar_time_derivative_at_diagonal_threshold T.toChain
      (fun m => (T.request m).epsCut) (fun m => (T.request m).Dcut)
      (fun m => (T.request m).mcut) (fun m => Classical.choice (T.extension m).retention)
      (fun m => (T.extension m).shift_eq) (fun m => (T.extension m).offset_eq)
      F hTower q hanti (diagonal_neckRadius_of_prefix_C11W4 T.toChain q hpref))

/-- consumer：narrow tuple（`exists_surgery_with_spatial_control_and_decay`）取 `S = T.toChain`
得 `(F, q, …)`，其 `hTower` / `hranti` / `hpref` 喂 `timeDerivativeSupply_of_blockTower_C11W4`，
得同一个 `(F, q)` 上的 S11（`a12Enhanced_of_chain_C11P2` 的 `hext` 里 `TimeDerivativeSupply_C11E` 一项）。 -/
example {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve) :
    ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = T.toChain.tower ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      TimeDerivativeSupply_C11E F q.neckRadius C.Ctime := by
  obtain ⟨F, q, -, -, hTower, -, -, -, -, hranti, hpref, -⟩ :=
    T.toChain.exists_surgery_with_spatial_control_and_decay
  exact ⟨F, q, hTower, hranti,
    timeDerivativeSupply_of_blockTower_C11W4 T F hTower q hranti
      (fun n t ht => (hpref n t ht).2.1)⟩

end GC.LongTime.Ch11
