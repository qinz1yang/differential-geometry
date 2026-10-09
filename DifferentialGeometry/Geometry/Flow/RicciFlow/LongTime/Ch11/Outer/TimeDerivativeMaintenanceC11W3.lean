import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepConsumerC11W
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative

set_option autoImplicit false

/-!
# S-CH11-W1L3 (G1)：`TimeDerivativeControl_C11W` 的逐块维护（L3）

outer 的 `blockStep_of_astraStepShape_C11W`（`Outer/BlockStepConsumerC11W`）只差 `hderiv`：
`Inv_C11W X` + `PhysicalExtension_C11W X Y ℓ req d` ⇒ `TimeDerivativeControl_C11W Y`。
本文件把它证成定理，只用已落地模块（`SH/PreparedSpatialStepDerivative` 的
`derivative_bound_on_old_native_tail`、`SH/PreparedSpatialState` 的 `PreparedSpatialSuccessor`），
常数仍是 Γ 的 `C.Ctime`。

对 `Y` 的第 `k` 个 stage 分两种情形（阈值 `(Y.radius²)⁻¹ ≥ (X.radius²)⁻¹`，因
`PreparedSpatialSuccessor.radius_le`）：
* `X.offset ≤ k`（old native tail；包括 `X.history` 末段与新延拓的全部 stage）：
  `PreparedSpatialStepRetention.derivative_bound_on_old_native_tail`（`oldNative_estimates`）。
* `k < X.offset`（`X` 的 native 起点之前，stage 在 `X.history` 中已闭）：`Inv X` 的
  `timeDerivative` 沿 `PreparedSpatialSuccessor.initial_prefix` 运输（`stageMetric` 在
  开区间上与 `X.history` 的对应 stage 同一 germ，`stageEndTime` 两边相同）。

* `derivative_bound_on_prefix_C11W3`：`k < X.offset` 的运输（只用 prefix，不用 retention）。
* `timeDerivativeControl_of_retention_C11W3`：数据级（successor + retention）形。
* `timeDerivativeControl_of_physicalExtension_C11W3` / `..._of_inv_physicalExtension_C11W3`：
  `PhysicalExtension_C11W` 形，正是 `hderiv` 的形状。
* `blockStep_of_astraStepShape_C11W3`：consumer，astra step 结论形（`hshape`）⇒
  `BlockStep_C11W j`，不再有 `hderiv` 前提。
-/

noncomputable section

open private event_samePresentation_of_prefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStepDerivative
open private overlapCastPoint overlapCastPoint_heq overlap_scalar_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Noncollapsing.SpatialWitnessTransport

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `k < X.offset` 的运输：`Y` 的第 `k` 个 stage 与 `X.history` 的第 `k` 个 stage 是同一个
actual stage（`PreparedSpatialSuccessor.initial_prefix`），故 `X` 上的导数界原样搬到 `Y`。
阈值只需 `(X.radius²)⁻¹` 版本。 -/
theorem derivative_bound_on_prefix_C11W3 {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {Y : BlockState_C11W pBase C P g (j + 1)}
    {activation eta d : ℝ} (hX : TimeDerivativeControl_C11W X)
    (hsucc : PreparedSpatialSuccessor X Y activation eta d)
    (k : Fin (Y.history.eventCount + 1)) (hk : k.val < X.offset)
    (y : (Y.history.stage k).Carrier) (s : ℝ)
    (hs : s ∈ Ioo (Y.history.time k) (Y.history.toHistory.stageEndTime k))
    (hscalar : (X.radius ^ 2)⁻¹ <
      metricScalarAt (Y.history.toHistory.stageMetric k s) y) :
    |derivWithin (fun v => metricScalarAt (Y.history.toHistory.stageMetric k v) y)
      (Iic s) s| ≤
      C.Ctime * metricScalarAt (Y.history.toHistory.stageMetric k s) y ^ 2 := by
  have hcount := X.affine.count_eq
  have hkOld : k.val < X.history.eventCount := by omega
  let iOld : Fin X.history.eventCount := ⟨k.val, hkOld⟩
  let iFull : Fin Y.history.eventCount := iOld.castLE hsucc.count_le
  have hkFull : k = iFull.castSucc := Fin.ext rfl
  have hPresent := event_samePresentation_of_prefix hsucc.initial_prefix.1 hsucc.count_le iOld
  have hStage : Y.history.stage k = X.history.stage iOld.castSucc :=
    (congrArg Y.history.stage hkFull).trans hPresent.incomingStage_eq
  have hTime : Y.history.toHistory.time k = X.history.toHistory.time iOld.castSucc := by
    rw [hkFull]
    exact hPresent.leftTime_eq
  have hEnd : Y.history.toHistory.stageEndTime k =
      X.history.toHistory.stageEndTime iOld.castSucc := by
    rw [hkFull, Y.history.toHistory.stageEndTime_castSucc,
      X.history.toHistory.stageEndTime_castSucc]
    exact hPresent.eventTime_eq
  have hsX : s ∈ Ioo (X.history.time iOld.castSucc)
      (X.history.toHistory.stageEndTime iOld.castSucc) := by
    rw [← hEnd]
    refine ⟨?_, hs.2⟩
    change X.history.toHistory.time iOld.castSucc < s
    rw [← hTime]
    exact hs.1
  let z := overlapCastPoint hStage y
  have hPoint : HEq y z := (overlapCastPoint_heq hStage y).symm
  have hMetric (u : ℝ)
      (hu : u ∈ Ioo (Y.history.time k) (Y.history.toHistory.stageEndTime k)) :
      HEq (Y.history.toHistory.stageMetric k u)
        (X.history.toHistory.stageMetric iOld.castSucc u) := by
    have hPrefix := hPresent.incomingMetric_heq u
      (by simpa only [hkFull, Y.history.toHistory.stageEndTime_castSucc] using
        (show u ∈ Ico (Y.history.time k) (Y.history.toHistory.stageEndTime k) from
          ⟨hu.1.le, hu.2⟩))
    have hY : HEq (Y.history.toHistory.stageMetric k u)
        ((Y.history.toHistory.event iFull).incoming.flow.base.metric u) := by
      rw [hkFull, ObservedHistory.stageMetric_castSucc_apply]
    have hXe : HEq (X.history.toHistory.stageMetric iOld.castSucc u)
        ((X.history.toHistory.event iOld).incoming.flow.base.metric u) := by
      rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hY.trans (hPrefix.trans hXe.symm)
  have hGerm : (fun v => metricScalarAt (Y.history.toHistory.stageMetric k v) y) =ᶠ[𝓝 s]
      (fun v => metricScalarAt (X.history.toHistory.stageMetric iOld.castSucc v) z) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
    exact overlap_scalar_eq hStage (hMetric u hu) hPoint
  have hscalarX : (X.radius ^ 2)⁻¹ <
      metricScalarAt (X.history.toHistory.stageMetric iOld.castSucc s) z := by
    rw [← hGerm.eq_of_nhds]
    exact hscalar
  have hBound := hX iOld.castSucc z s hsX hscalarX
  rw [hGerm.derivWithin_eq_of_nhds, hGerm.eq_of_nhds]
  exact hBound

/-- **逐块维护（数据级形）**：`X` 满足 `TimeDerivativeControl_C11W`，`Y` 是 `X` 的
`PreparedSpatialSuccessor`（restart 等式 `Y.shift` / `Y.offset`）并带 retention（old native
延拓 + `NativeEstimates`）⇒ `Y` 满足 `TimeDerivativeControl_C11W`；常数仍是 `C.Ctime`。 -/
theorem timeDerivativeControl_of_retention_C11W3 {j : ℕ}
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
  by_cases hk : X.offset ≤ k.val
  · exact W.derivative_bound_on_old_native_tail hsucc hshift hoffset k hk y s hs
      (hr.trans_lt hscalar)
  · exact derivative_bound_on_prefix_C11W3 hX hsucc k (Nat.lt_of_not_le hk) y s hs
      (hr.trans_lt hscalar)

/-- **`hderiv` 的形状**：`TimeDerivativeControl_C11W` 沿 `PhysicalExtension_C11W` 传递。 -/
theorem timeDerivativeControl_of_physicalExtension_C11W3 {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {Y : BlockState_C11W pBase C P g (j + 1)}
    {ℓ : BlockLookahead_C11W X} {req : BlockRequest_C11W} {d : ℝ}
    (hX : TimeDerivativeControl_C11W X) (hPE : PhysicalExtension_C11W X Y ℓ req d) :
    TimeDerivativeControl_C11W Y := by
  obtain ⟨W⟩ := hPE.retention
  exact timeDerivativeControl_of_retention_C11W3 hX hPE.successor hPE.shift_eq hPE.offset_eq W

/-- 同上，直接以 `Inv_C11W X` 为前提（`blockStep_of_astraStepShape_C11W` 的 `hderiv`）。 -/
theorem timeDerivativeControl_of_inv_physicalExtension_C11W3 {Cdist : ℝ≥0}
    {cMax Dstar εReserve : ℝ} {j : ℕ}
    {X : BlockState_C11W pBase C P g j} {Y : BlockState_C11W pBase C P g (j + 1)}
    {ℓ : BlockLookahead_C11W X} {req : BlockRequest_C11W} {d : ℝ}
    (hX : Inv_C11W Cdist cMax Dstar εReserve X) (hPE : PhysicalExtension_C11W X Y ℓ req d) :
    TimeDerivativeControl_C11W Y :=
  timeDerivativeControl_of_physicalExtension_C11W3 hX.timeDerivative hPE

/-- **consumer**：astra step 结论形（`hshape`，与 `blockStep_of_astraStepShape_C11W` 的同名前提
逐字同）⇒ `BlockStep_C11W j`；`hderiv` 已由本文件的维护引理 discharge。 -/
theorem blockStep_of_astraStepShape_C11W3 {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ} (j : ℕ)
    (hshape : ∀ X : BlockState_C11W pBase C P g j, X.DistanceData Cdist →
      ∃ ℓ : BlockLookahead_C11W X,
        ℓ.nextClass.HasReserveQuality Dstar εReserve ∧ ℓ.nextClass.HasDistanceExtension Cdist ∧
        0 < ℓ.rNext ∧ ℓ.rNext ≤ X.radius ∧ ℓ.nextClass.Qall ≤ (ℓ.rNext ^ 2)⁻¹ ∧
        ℓ.rNext * Real.sqrt ℓ.nextClass.Qall ≤ 100 * cMax ∧
        ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
        ∀ accuracyCap : ℝ, 0 < accuracyCap →
          ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ X.parameters.delta (preparedSpatialHorizon j) ∧
            d ≤ accuracyCap ∧
          ∃ Y : BlockState_C11W pBase C P g (j + 1),
            Y.radius = ℓ.rNext ∧ Y.shift = X.history.time (Fin.last X.history.eventCount) ∧
            Y.offset = X.history.eventCount ∧
            Y.nativeStage = X.native.stage (Fin.last X.native.eventCount) ∧
            HEq Y.nativeMetric (X.native.initialMetric (Fin.last X.native.eventCount)) ∧
            HEq Y.prepared ℓ.nextClass ∧ Y.DistanceData Cdist ∧
            PreparedSpatialSuccessor X Y ((5 / 6 : ℝ) * 3 ^ j) (1 / ((j : ℝ) + 2)) d ∧
            Nonempty (PreparedSpatialStepRetention X Y d (1 / ((j : ℝ) + 2)) εcut Dcut mcut)) :
    BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j :=
  blockStep_of_astraStepShape_C11W j hshape
    fun _ _ _ _ _ hX hPE => timeDerivativeControl_of_inv_physicalExtension_C11W3 hX hPE

/-- consumer（端到端）：astra step 结论形对每个块 `j` 成立 + capacity 1 的 prepared class + S8
⇒ A12。W1–W4 里 `TimeDerivativeControl` 的维护不再是前提（`hderiv` 已 discharge）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (hcMax : 0 < cMax)
    (prepared : ClosedBirthPreparedClass pBase C P g 1) (hbase : prepared.parameters = pBase)
    (hprepared : prepared.HasDistanceExtension Cdist)
    (hres : prepared.HasReserveQuality Dstar εReserve)
    (hshape : ∀ j : ℕ, ∀ X : BlockState_C11W pBase C P g j, X.DistanceData Cdist →
      ∃ ℓ : BlockLookahead_C11W X,
        ℓ.nextClass.HasReserveQuality Dstar εReserve ∧ ℓ.nextClass.HasDistanceExtension Cdist ∧
        0 < ℓ.rNext ∧ ℓ.rNext ≤ X.radius ∧ ℓ.nextClass.Qall ≤ (ℓ.rNext ^ 2)⁻¹ ∧
        ℓ.rNext * Real.sqrt ℓ.nextClass.Qall ≤ 100 * cMax ∧
        ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
        ∀ accuracyCap : ℝ, 0 < accuracyCap →
          ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ X.parameters.delta (preparedSpatialHorizon j) ∧
            d ≤ accuracyCap ∧
          ∃ Y : BlockState_C11W pBase C P g (j + 1),
            Y.radius = ℓ.rNext ∧ Y.shift = X.history.time (Fin.last X.history.eventCount) ∧
            Y.offset = X.history.eventCount ∧
            Y.nativeStage = X.native.stage (Fin.last X.native.eventCount) ∧
            HEq Y.nativeMetric (X.native.initialMetric (Fin.last X.native.eventCount)) ∧
            HEq Y.prepared ℓ.nextClass ∧ Y.DistanceData Cdist ∧
            PreparedSpatialSuccessor X Y ((5 / 6 : ℝ) * 3 ^ j) (1 / ((j : ℝ) + 2)) d ∧
            Nonempty (PreparedSpatialStepRetention X Y d (1 / ((j : ℝ) + 2)) εcut Dcut mcut))
    (hS8 : ∀ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
      ∀ F : GC.Interface.RawSurgery P g, F.tower = T.toChain.tower →
        LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A T.toChain).delta
          (diagonalAccuracy_C11S (chainDiagonal_C11A T.toChain).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  a12_of_preparedBase_C11W P g pBase C Cdist cMax Dstar εReserve hcMax prepared hbase hprepared
    hres (fun j => blockStep_of_astraStepShape_C11W3 j (hshape j)) hS8

end GC.LongTime.Ch11
