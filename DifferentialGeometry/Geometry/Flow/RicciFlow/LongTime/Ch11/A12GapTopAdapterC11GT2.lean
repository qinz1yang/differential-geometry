import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateCoreP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.S15.SliceBridgeC11S15
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialStatePortC11P

set_option autoImplicit false

/-!
# S-CH11-GAPTOP2 G3 / G4：`CanonicalLateCore` adapter 与 `εK` 阈值来源（后缀 `_C11GT2`）

## G3：`CanonicalLateCore_P6X ⇒ LargerBallCanonicalLateSupply_C11E`（R-C11-6 D-13(3)）
`hP6b` 的类型换成 P6SEL 的 (b) 最小合同 `CanonicalLateCore_P6X`（`P6LateCoreP6X`），但 `hspine` 的输入、
`s8_of_smallVol_C11V4` 的 `hP6`、`a12EnhancedFull_of_chain_C12X` 的 P6 (b) 字段都仍是 RegularSlice 形
`LargerBallCanonicalLateSupply_C11E`，所以不是纯签名替换，要一个 adapter。

* `canonicalLateCore_iff_P6X` 说 `CanonicalLateCore_P6X ↔ LargerBallCanonicalLateSupply_P6A`
  （`Iff.rfl`，history late 形）；
* S15 G2a 桥 `largerBallCanonicalLateSupply_of_history_C11S15` 把 history late 形（**全部 `A > 0`、全部
  `n`、全部 `t ∈ Icc 0 horizon` 且 `T ≤ t`**）搬成 RegularSlice 形：slice 的 history 就是
  `(F.tower.history ⌈s.time⌉).restrict cut`（`slice_history_restrict_CX2 := rfl`），
  `hasSmallParabolicCurvature`、ball / 体积 / 点沿 `HEq` 传递；
* 所以 adapter **不需要任何额外的 boundary / 全时刻 binder**（简报里的 `hbound` 不出现）：全时刻条件
  `T ≤ t` 与 `A > 0` 已在 `CanonicalLateCore_P6X` 的形里，桥给出 RegularSlice 的 `T ≤ s.time`。

## G4：`εK` 阈值从各 producer 取（R-C11-6 D-13(4)）
旧版 `εK` 是自由参数 `hεK : ∀ Γ, 0 < εK Γ`，且 binder 只说"对 `pB.modelAccuracy ≤ εK Γ` 成立"。审稿：
`εK` 自由不等于"任意正值都能使 producer 成立"，producer 须对**实际选的** `εK` 证全称结论，阈值从 producer
定理取。新版每个依赖阈值的 binder（`hK / hspine / hP6b / hfull`）自带 `∃ ε_i`（含 `∀ Γ, 0 < ε_i Γ`），
顶层的 `εK` 不再自由，而是
`εK_threshold_C11GT2 εκ εsp εP6 εfull Γ := min (min (εκ Γ) (εsp Γ)) (min (εP6 Γ) (εfull Γ))`，
`pB.modelAccuracy ≤ εK_threshold` ⇒ 四个 producer 的各自阈值条件（`εK_threshold_le_C11GT2`）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped ENNReal
open GC.GeneralFlow

namespace GC.LongTime.Ch11

universe u

/-- **G3 adapter**：P6 (b) 的最小 history 合同 `CanonicalLateCore_P6X`（P6SEL）⇒ RegularSlice 形
`LargerBallCanonicalLateSupply_C11E`（`hspine` / `hS8wire` / `a12EnhancedFull_of_chain_C12X` 的
P6 (b) 形）。无额外前提：S15 G2a 桥已是全 `A > 0`、全 `t ≥ T` 的 history ⇒ slice。 -/
theorem largerBallCanonicalLateSupply_of_core_C11GT2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} (h : CanonicalLateCore_P6X F ε C1 C2) :
    LargerBallCanonicalLateSupply_C11E F ε C1 C2 :=
  largerBallCanonicalLateSupply_of_history_C11S15 (canonicalLateCore_iff_P6X.1 h)

/-- consumer：adapter 后 (b) 在 `s ∈ RegularSlice`、晚期 `T ≤ s.time` 的 `A > 0` 形上可用
（`hspine` 的 `hb` 入口形）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} (h : CanonicalLateCore_P6X F ε C1 C2) (A : ℝ) (hA : 0 < A) :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧ ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt ⟨s.time, s.positive.le, le_rfl⟩).Carrier) (r : ℝ),
        2 * r ^ 2 < s.time →
        GC.LongTime.hasSmallParabolicCurvature s.history ⟨s.time, s.positive.le, le_rfl⟩ p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (s.history.stageMetric
          (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) p r →
        ∀ y ∈ riemannianBallOf (s.history.stageMetric
          (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) p (A * r),
          K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (s.history.stageMetric
            (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) y →
          ∃ W : SpatialCanonicalWitness (s.history.stageMetric
            (s.history.activeStage ⟨s.time, s.positive.le, le_rfl⟩) s.time) ε C1 C2 y,
            W.capTubeHasNeckChart ε :=
  largerBallCanonicalLateSupply_of_core_C11GT2 h A hA

/-- **G4 阈值**：四个 producer（κ / spine / P6 (b) / S16 full）各自给的 `ClosedBirthConstants → ℝ`
阈值的逐点 min。顶层以它代替旧版自由的 `εK`。 -/
def εK_threshold_C11GT2 (εκ εsp εP6 εfull : ClosedBirthConstants → ℝ) (Γ : ClosedBirthConstants) :
    ℝ :=
  min (min (εκ Γ) (εsp Γ)) (min (εP6 Γ) (εfull Γ))

/-- 四个 producer 阈值都为正 ⇒ 合成阈值为正。 -/
theorem εK_threshold_pos_C11GT2 {εκ εsp εP6 εfull : ClosedBirthConstants → ℝ}
    (h₁ : ∀ Γ, 0 < εκ Γ) (h₂ : ∀ Γ, 0 < εsp Γ) (h₃ : ∀ Γ, 0 < εP6 Γ) (h₄ : ∀ Γ, 0 < εfull Γ)
    (Γ : ClosedBirthConstants) : 0 < εK_threshold_C11GT2 εκ εsp εP6 εfull Γ :=
  lt_min (lt_min (h₁ Γ) (h₂ Γ)) (lt_min (h₃ Γ) (h₄ Γ))

/-- 合成阈值 ≤ 每个 producer 的阈值：`x ≤ εK_threshold` 给出四个 producer 各自的 `x ≤ ε_i`。 -/
theorem εK_threshold_le_C11GT2 (εκ εsp εP6 εfull : ClosedBirthConstants → ℝ)
    (Γ : ClosedBirthConstants) {x : ℝ} (hx : x ≤ εK_threshold_C11GT2 εκ εsp εP6 εfull Γ) :
    x ≤ εκ Γ ∧ x ≤ εsp Γ ∧ x ≤ εP6 Γ ∧ x ≤ εfull Γ :=
  ⟨(hx.trans (min_le_left _ _)).trans (min_le_left _ _),
    (hx.trans (min_le_left _ _)).trans (min_le_right _ _),
    (hx.trans (min_le_right _ _)).trans (min_le_left _ _),
    (hx.trans (min_le_right _ _)).trans (min_le_right _ _)⟩

/-- consumer：四个 producer 的 `∃ ε_i` 形（每个都带 `∀ Γ, 0 < ε_i Γ`）⇒ 一个正阈值，它满足四个 producer 的
阈值条件（顶层 `a12EnhancedFull_of_gaps_v2_C11GT2` 用的就是这个选法）。 -/
example (S₁ S₂ S₃ S₄ : (ClosedBirthConstants → ℝ) → Prop)
    (h₁ : ∃ ε : ClosedBirthConstants → ℝ, (∀ Γ, 0 < ε Γ) ∧ S₁ ε)
    (h₂ : ∃ ε : ClosedBirthConstants → ℝ, (∀ Γ, 0 < ε Γ) ∧ S₂ ε)
    (h₃ : ∃ ε : ClosedBirthConstants → ℝ, (∀ Γ, 0 < ε Γ) ∧ S₃ ε)
    (h₄ : ∃ ε : ClosedBirthConstants → ℝ, (∀ Γ, 0 < ε Γ) ∧ S₄ ε) :
    ∃ εK : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εK Γ) ∧
      ∃ εκ εsp εP6 εfull : ClosedBirthConstants → ℝ,
        εK = εK_threshold_C11GT2 εκ εsp εP6 εfull ∧ S₁ εκ ∧ S₂ εsp ∧ S₃ εP6 ∧ S₄ εfull := by
  obtain ⟨εκ, p₁, s₁⟩ := h₁
  obtain ⟨εsp, p₂, s₂⟩ := h₂
  obtain ⟨εP6, p₃, s₃⟩ := h₃
  obtain ⟨εfull, p₄, s₄⟩ := h₄
  exact ⟨εK_threshold_C11GT2 εκ εsp εP6 εfull, εK_threshold_pos_C11GT2 p₁ p₂ p₃ p₄,
    εκ, εsp, εP6, εfull, rfl, s₁, s₂, s₃, s₄⟩

end GC.LongTime.Ch11
