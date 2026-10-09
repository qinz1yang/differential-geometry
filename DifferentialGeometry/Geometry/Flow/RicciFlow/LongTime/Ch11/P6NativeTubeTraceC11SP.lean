import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeWindowTubeC11SP

/-!
# 合同 X ⇐ trace 逐点局部 Dt（统一局部 Dt 合同；O-CH11-NATIVE-NR G3c，后缀 `_C11SP`）

G2 孪生的合同 X 要一族开集 `W j` 覆盖起点在锚集 `U`（`= Jbig '' {‖z‖ < R+1}`）里的 backward traces，
Dt 在 `W j` 上。本文件说明：**只要锚集 `U` 开，trace 集合本身就是开的**
（`= val '' (backwardSurvivorMap⁻¹ U)`，survivor 域开、survivor 映射连续），所以 X 可以由
"在起点落在 `U` 的 trace 的点上逐点 Dt" 直接给出——与 SLTLOCAL `hslabsLoc`（终端锚球的 traces 上逐点 Dt）
同一种形状，只是锚在 birth 端而不是终端。统一合同：Dt 在"穿过开锚集的 traces 的点"上、自身尺度时间窗内。
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

/-- trace tube：起点在开集 `U` 里的 backward traces 的端点集合是开集。 -/
theorem isOpen_traceTube_C11SP (H : ObservedHistory.{u}) (first j : Fin (H.eventCount + 1))
    {U : Set (H.stage first).Carrier} (hU : IsOpen U) :
    IsOpen {x : (H.stage j).Carrier |
      ∃ (hf : first ≤ j) (A : BackwardPointTrace H first j hf x), A.point first le_rfl hf ∈ U} := by
  by_cases hf : first ≤ j
  · have hset : {x : (H.stage j).Carrier |
        ∃ (hf : first ≤ j) (A : BackwardPointTrace H first j hf x), A.point first le_rfl hf ∈ U} =
        Subtype.val '' ((H.backwardSurvivorMap first j hf first le_rfl hf) ⁻¹' U) := by
      ext x
      constructor
      · rintro ⟨hf', A, hA⟩
        refine ⟨⟨x, ⟨A⟩⟩, ?_, rfl⟩
        change H.backwardSurvivorMap first j hf first le_rfl hf ⟨x, ⟨A⟩⟩ ∈ U
        rw [H.backwardSurvivorMap_eq_point first j hf first le_rfl hf ⟨x, ⟨A⟩⟩ A]
        exact hA
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hf, Classical.choice z.property, hz⟩
    rw [hset]
    apply (H.backwardSurvivorDomain first j hf).isOpen.isOpenMap_subtype_val
    exact hU.preimage
      (H.backwardSurvivorMap_isSmoothEmbedding first j hf first le_rfl hf).contMDiff.continuous
  · have hset : {x : (H.stage j).Carrier |
        ∃ (hf : first ≤ j) (A : BackwardPointTrace H first j hf x), A.point first le_rfl hf ∈ U} =
        ∅ := by
      ext x
      exact ⟨fun ⟨hf', _⟩ => (hf hf').elim, fun h => h.elim⟩
    rw [hset]
    exact isOpen_empty

/-- **合同 X ⇐ trace 逐点 Dt**：取 `W j :=` trace tube，`hW`、`htube` 自动成立；Dt 在 `W` 上
等价于在"起点落在 `U` 的 traces 的点"上逐点 Dt。 -/
theorem tube_of_tracewise_C11SP (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    {U : Set (H.stage first).Carrier} (hU : IsOpen U) :
    let W : ∀ j : Fin (H.eventCount + 1), Set (H.stage j).Carrier := fun j =>
      {x | ∃ (hf : first ≤ j) (A : BackwardPointTrace H first j hf x), A.point first le_rfl hf ∈ U}
    (∀ j, IsOpen (W j)) ∧
    (∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j), j ≤ last →
      ∀ (x : (H.stage j).Carrier) (A : BackwardPointTrace H first j hf x),
        A.point first le_rfl hf ∈ U → x ∈ W j) ∧
    (∀ (j : Fin (H.eventCount + 1)) (x : (H.stage j).Carrier), x ∈ W j →
      ∃ (hf : first ≤ j) (A : BackwardPointTrace H first j hf x), A.point first le_rfl hf ∈ U) :=
  ⟨fun j => isOpen_traceTube_C11SP H first j hU,
    fun _ hf _ _ A hA => ⟨hf, A, hA⟩, fun _ _ hx => hx⟩

/-- consumer：trace 逐点 Dt（起点在开锚集 `U`）⇒ G2 孪生要的 "Dt on `W`" 形（`W :=` trace tube，
配合 `tube_of_tracewise_C11SP` 的 `hW` / `htube` 即付清合同 X 的三个 binder）。 -/
theorem dt_on_traceTube_of_tracewise_C11SP (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) {U : Set (H.stage first).Carrier} {q₀ : ℝ} {C : ℝ≥0}
    (hDt : ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, j.succ ≤ last →
      ∀ (x : (H.stage j.castSucc).Carrier) (A : BackwardPointTrace H first j.castSucc hf x),
        A.point first le_rfl hf ∈ U →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2) :
    ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ x : (H.stage j.castSucc).Carrier,
        x ∈ {x : (H.stage j.castSucc).Carrier | ∃ (hf : first ≤ j.castSucc)
          (A : BackwardPointTrace H first j.castSucc hf x), A.point first le_rfl hf ∈ U} →
      ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
        q₀ < (H.event j).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
          C * (H.event j).incoming.flow.scalar t x ^ 2 := by
  intro j _ hl x hx
  obtain ⟨hf, A, hA⟩ := hx
  exact hDt j hf hl x A hA

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
