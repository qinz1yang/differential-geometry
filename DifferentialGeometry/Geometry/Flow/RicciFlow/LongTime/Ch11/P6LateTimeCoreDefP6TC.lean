import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X

/-!
# history-level 时间版 late core：`CanonicalLateTimeCore_P6X`（O-CH11-P6TIME G1，后缀 `_P6TC`）

R-C11-14 D-2（lead 处置，Q1(a) 修正版）：在 P6(b) 证明层保留 history-level 的时间控制输出。
* **`CanonicalLateTimeCore_P6X`**：`CanonicalLateCore_P6X`（P6LateCoreP6X.lean L44–63）的全部前件与量词序
  `∀ A > 0, ∃ K₁ T > 0, ∀ n t p r y` 逐字，仍在同一 `H = (F.tower.history n).toHistory` 内评价；
  加参数 `Ctime : ℝ≥0`，最后的空间输出换成完整 Good
  `H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y`（CanonicalTimeControlPointSelection
  L44–53：空间 witness ∧ 实际 history 的单侧时间导数界，前件 `time (activeStage t) < t → t < horizon`）。
* **`canonicalLateCore_of_timeCore_P6TC`**（PROVED）：空间投影 TimeCore ⇒ 旧 `CanonicalLateCore_P6X`
  （取 HSCTC 的第一分量）。反方向不声称（D-1：不能从空间 core 推时间导数界）。
不经 RegularSlice（D-2 禁止：slice 测试时刻 = horizon，时间分量空真）。
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set Filter
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

/-- **时间版 (b) 合同**（R-C11-14 D-2）：`CanonicalLateCore_P6X` 的前件与量词序逐字，加 `Ctime`，
输出 history-level 的 `HasSpatialCanonicalTimeControl`（空间 witness ∧ 时间导数界）。 -/
def CanonicalLateTimeCore_P6X
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g)
    (ε C1 C2 : ℝ) (Ctime : ℝ≥0) : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ K1 T : ℝ, 0 < K1 ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon)
        (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf
            (H.stageMetric (H.activeStage t) t) p (A * r),
          K1 * (r ^ 2)⁻¹ ≤
            metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y

/-- **空间投影**：时间版 ⇒ 旧 `CanonicalLateCore_P6X`（同 `K₁ T`，取 HSCTC 的空间分量）。 -/
theorem canonicalLateCore_of_timeCore_P6TC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime) : CanonicalLateCore_P6X F ε C1 C2 := by
  intro A hA
  obtain ⟨K1, T, hK1, hT, hB⟩ := h A hA
  exact ⟨K1, T, hK1, hT, fun n t p r hTt ht hs hv y hy hK => (hB n t p r hTt ht hs hv y hy hK).1⟩

/-- 投影也落到 P6A 的 `LargerBallCanonicalLateSupply_P6A`（`canonicalLateCore_iff_P6X`）。 -/
theorem largerBallCanonicalLateSupply_of_timeCore_P6TC {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime) :
    LargerBallCanonicalLateSupply_P6A F ε C1 C2 :=
  canonicalLateCore_iff_P6X.mp (canonicalLateCore_of_timeCore_P6TC h)

end GC.LongTime.Ch11
