import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection

/-!
# 边界点分情形：位置四分 + 边界处 `Good ⟺ spatial witness`（S-CH11-P6BND G3，后缀 `_P6S`）

P6 收口主形（event slab：`false_of_selection_eventSlab_Kdata_ctrl_P6M2` / `…_noRt_P6S`；final slab：
`false_of_selection_finalSlab_Kdata_P6S`）都要求坏点 `σ n` 落在 slab **内部**：
`time j.castSucc < t < time j.succ`（event）或 `time last < t < horizon`（final）。本文件把"分情形"
形式化，并给出边界点上最关键的结构事实：

1. `exists_position_P6S`：任意 `σ ∈ [0, horizon]` 恰落在四类之一——event slab 内部 / final slab 内部 /
   某个 stage 时刻 `time m` / 视界 `horizon`（前两类 = 现有主形；后两类 = 边界点）。
2. `exists_strictMono_position_P6S`：任意坏点序列有子列整条落在同一类（无限鸽笼）。
3. `hasSpatialCanonicalTimeControl_iff_of_boundary_P6S`：边界点（`time (activeStage v) = v` 或
   `v = horizon`）上 `HasSpatialCanonicalTimeControl` 的**时间导数分量空真**
   （其前提 `time (activeStage v) < v < horizon` 不成立），故
   `Good ⟺ ∃ spatial witness`；于是 `hsel : ¬ Good` 在边界点上就是 `¬ ∃ W, …`
   （`not_hasSpatialCanonicalTimeControl_iff_of_boundary_P6S`）。这正是 K-route 当初为
   interior 点绕开 P6D2 G4（`hsel` 在 extendAt 视界上、Good 的时间分量空真）的那个量，
   在边界点上两条路线的 `¬Good` 一致。
**未做（见 DELIVERIES G3 块）**：边界两类的收口本身——它们不是纯机械的：SLT / anchor 需要
`time last < t`（slab 内正年龄），而边界点 `t = time m`（stage 初）或 `t = horizon`
（final slab 的闭端、`IncomingSlab` 是 `Ico`）没有这段年龄。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **位置四分**：`σ ∈ [0, horizon]` 落在 event slab 内部 / final slab 内部 / 某个 stage 时刻 /
视界（后两类可能重合，如 `horizon = time last`）。 -/
theorem exists_position_P6S (H : ObservedHistory.{u}) (σ : Icc (0 : ℝ) H.horizon) :
    (∃ j : Fin H.eventCount, H.time j.castSucc < (σ : ℝ) ∧ (σ : ℝ) < H.time j.succ) ∨
    (H.time (Fin.last H.eventCount) < (σ : ℝ) ∧ (σ : ℝ) < H.horizon) ∨
    (∃ m : Fin (H.eventCount + 1), (σ : ℝ) = H.time m) ∨ (σ : ℝ) = H.horizon := by
  by_cases hs : H.time (H.activeStage σ) = (σ : ℝ)
  · exact Or.inr (Or.inr (Or.inl ⟨H.activeStage σ, hs.symm⟩))
  have hlt : H.time (H.activeStage σ) < (σ : ℝ) := lt_of_le_of_ne (H.activeStage_time_le σ) hs
  by_cases hk : (H.activeStage σ).val < H.eventCount
  · refine Or.inl ⟨⟨(H.activeStage σ).val, hk⟩, ?_, ?_⟩
    · have hc : (⟨(H.activeStage σ).val, hk⟩ : Fin H.eventCount).castSucc = H.activeStage σ :=
        Fin.ext rfl
      rw [hc]
      exact hlt
    · have hn := H.activeStage_before_next σ hk
      have hc : (⟨(H.activeStage σ).val, hk⟩ : Fin H.eventCount).succ =
          (⟨(H.activeStage σ).val + 1, by omega⟩ : Fin (H.eventCount + 1)) := Fin.ext rfl
      rw [hc]
      exact hn
  · have hlast : H.activeStage σ = Fin.last H.eventCount :=
      Fin.ext (by have := (H.activeStage σ).isLt; simp only [Fin.val_last]; omega)
    rw [hlast] at hlt
    rcases lt_or_eq_of_le σ.2.2 with h | h
    · exact Or.inr (Or.inl ⟨hlt, h⟩)
    · exact Or.inr (Or.inr (Or.inr h))

/-- **子列版位置四分**：坏点序列 `σ n` 有子列整条落在同一类。 -/
theorem exists_strictMono_position_P6S {Kh : ℕ → ObservedHistory.{u}}
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ n, ∃ j : Fin (Kh (ψ n)).eventCount, (Kh (ψ n)).time j.castSucc < (σ (ψ n) : ℝ) ∧
          (σ (ψ n) : ℝ) < (Kh (ψ n)).time j.succ) ∨
        (∀ n, (Kh (ψ n)).time (Fin.last (Kh (ψ n)).eventCount) < (σ (ψ n) : ℝ) ∧
          (σ (ψ n) : ℝ) < (Kh (ψ n)).horizon) ∨
        (∀ n, ∃ m : Fin ((Kh (ψ n)).eventCount + 1), (σ (ψ n) : ℝ) = (Kh (ψ n)).time m) ∨
        (∀ n, (σ (ψ n) : ℝ) = (Kh (ψ n)).horizon)) := by
  let P₁ : ℕ → Prop := fun n => ∃ j : Fin (Kh n).eventCount, (Kh n).time j.castSucc < (σ n : ℝ) ∧
    (σ n : ℝ) < (Kh n).time j.succ
  let P₂ : ℕ → Prop := fun n => (Kh n).time (Fin.last (Kh n).eventCount) < (σ n : ℝ) ∧
    (σ n : ℝ) < (Kh n).horizon
  let P₃ : ℕ → Prop := fun n => ∃ m : Fin ((Kh n).eventCount + 1), (σ n : ℝ) = (Kh n).time m
  let P₄ : ℕ → Prop := fun n => (σ n : ℝ) = (Kh n).horizon
  by_cases h₁ : (Set.ofPred P₁).Infinite
  · exact ⟨Nat.nth P₁, Nat.nth_strictMono h₁, Or.inl fun n => Nat.nth_mem_of_infinite h₁ n⟩
  by_cases h₂ : (Set.ofPred P₂).Infinite
  · exact ⟨Nat.nth P₂, Nat.nth_strictMono h₂, Or.inr (Or.inl fun n => Nat.nth_mem_of_infinite h₂ n)⟩
  by_cases h₃ : (Set.ofPred P₃).Infinite
  · exact ⟨Nat.nth P₃, Nat.nth_strictMono h₃,
      Or.inr (Or.inr (Or.inl fun n => Nat.nth_mem_of_infinite h₃ n))⟩
  by_cases h₄ : (Set.ofPred P₄).Infinite
  · exact ⟨Nat.nth P₄, Nat.nth_strictMono h₄,
      Or.inr (Or.inr (Or.inr fun n => Nat.nth_mem_of_infinite h₄ n))⟩
  exfalso
  have hfin : (Set.ofPred P₁ ∪ Set.ofPred P₂ ∪ Set.ofPred P₃ ∪ Set.ofPred P₄).Finite :=
    (((Set.not_infinite.mp h₁).union (Set.not_infinite.mp h₂)).union
      (Set.not_infinite.mp h₃)).union (Set.not_infinite.mp h₄)
  refine Set.infinite_univ (hfin.subset fun n _ => ?_)
  rcases exists_position_P6S (Kh n) (σ n) with h | h | h | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **边界点上 `Good ⟺ spatial witness`**：`time (activeStage v) = v` 或 `v = horizon` 时，
`HasSpatialCanonicalTimeControl` 的时间导数分量（前提 `time (activeStage v) < v < horizon`）空真。 -/
theorem hasSpatialCanonicalTimeControl_iff_of_boundary_P6S {H : ObservedHistory.{u}}
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0} {v : Icc (0 : ℝ) H.horizon} {z : (H.stageAt v).Carrier}
    (hb : H.time (H.activeStage v) = (v : ℝ) ∨ (v : ℝ) = H.horizon) :
    H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z ↔
      ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun h1 h2 => ?_⟩⟩
  rcases hb with hb | hb
  · exact absurd hb h1.ne
  · exact absurd hb h2.ne

/-- 边界点上 `hsel : ¬ Good` 就是 `¬ ∃ spatial witness`（selection 的坏点在边界点上只可能坏在
空间分量）。 -/
theorem not_hasSpatialCanonicalTimeControl_iff_of_boundary_P6S {H : ObservedHistory.{u}}
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0} {v : Icc (0 : ℝ) H.horizon} {z : (H.stageAt v).Carrier}
    (hb : H.time (H.activeStage v) = (v : ℝ) ∨ (v : ℝ) = H.horizon) :
    ¬ H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z ↔
      ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps :=
  not_congr (hasSpatialCanonicalTimeControl_iff_of_boundary_P6S hb)

/-- stage 时刻 `σ = time m` 是边界点（`activeStage (stageTime m) = m`）。 -/
theorem boundary_of_stageTime_P6S (H : ObservedHistory.{u}) (m : Fin (H.eventCount + 1)) :
    H.time (H.activeStage (H.stageTime m)) = ((H.stageTime m : Icc (0 : ℝ) H.horizon) : ℝ) := by
  rw [H.activeStage_stageTime]
  rfl

/-- 视界 `σ = horizon` 是边界点。 -/
theorem boundary_of_horizon_P6S (H : ObservedHistory.{u}) :
    (((⟨H.horizon, H.horizon_nonneg, le_rfl⟩ : Icc (0 : ℝ) H.horizon)) : ℝ) = H.horizon := rfl

/-- 位置类 "stage 时刻或视界" ⇒ 边界点。 -/
theorem boundary_of_position_P6S (H : ObservedHistory.{u}) {σ : Icc (0 : ℝ) H.horizon}
    (h : (∃ m : Fin (H.eventCount + 1), (σ : ℝ) = H.time m) ∨ (σ : ℝ) = H.horizon) :
    H.time (H.activeStage σ) = (σ : ℝ) ∨ (σ : ℝ) = H.horizon := by
  rcases h with ⟨m, hm⟩ | h
  · refine Or.inl ?_
    have hσ : σ = H.stageTime m := Subtype.ext hm
    subst hσ
    exact H.boundary_of_stageTime_P6S m
  · exact Or.inr h

/-- **consumer**：坏点序列整条落在边界类（stage 时刻或视界）时，selection 的 `hsel : ¬ Good`
逐 `n` 化为 `¬ ∃ spatial witness`。 -/
theorem not_exists_witness_of_boundary_class_P6S {Kh : ℕ → ObservedHistory.{u}}
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0} {σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
    {y : ∀ n, ((Kh n).stageAt (σ n)).Carrier}
    (hpos : ∀ n, (∃ m : Fin ((Kh n).eventCount + 1), (σ n : ℝ) = (Kh n).time m) ∨
      (σ n : ℝ) = (Kh n).horizon)
    (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (σ n) (y n)) (n : ℕ) :
    ¬ ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        eps C1 C2 (y n), W.capTubeHasNeckChart eps :=
  (not_hasSpatialCanonicalTimeControl_iff_of_boundary_P6S
    ((Kh n).boundary_of_position_P6S (hpos n))).mp (hsel n)

/-- **分情形主定理（selection 序列）**：任意 selection 坏点序列有子列，要么整条落在 event slab
内部（喂 `false_of_selection_eventSlab_Kdata_ctrl_noRt_P6S`），要么整条落在 final slab 内部
（喂 `false_of_selection_finalSlab_Kdata_noRt_P6S`），要么整条是边界点（stage 时刻 / 视界）且
`hsel` 逐项化为 `¬ ∃ spatial witness`（边界类收口尚未做，见文件头）。 -/
theorem exists_strictMono_interior_or_boundary_P6S {Kh : ℕ → ObservedHistory.{u}}
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0} (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (hsel : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (σ n) (y n)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ n, ∃ j : Fin (Kh (ψ n)).eventCount, (Kh (ψ n)).time j.castSucc < (σ (ψ n) : ℝ) ∧
          (σ (ψ n) : ℝ) < (Kh (ψ n)).time j.succ) ∨
        (∀ n, (Kh (ψ n)).time (Fin.last (Kh (ψ n)).eventCount) < (σ (ψ n) : ℝ) ∧
          (σ (ψ n) : ℝ) < (Kh (ψ n)).horizon) ∨
        (∀ n, ¬ ∃ W : SpatialCanonicalWitness ((Kh (ψ n)).stageMetric
            ((Kh (ψ n)).activeStage (σ (ψ n))) (σ (ψ n))) eps C1 C2 (y (ψ n)),
          W.capTubeHasNeckChart eps)) := by
  obtain ⟨ψ, hψ, h | h | h | h⟩ := exists_strictMono_position_P6S σ
  · exact ⟨ψ, hψ, Or.inl h⟩
  · exact ⟨ψ, hψ, Or.inr (Or.inl h)⟩
  · exact ⟨ψ, hψ, Or.inr (Or.inr fun n =>
      not_exists_witness_of_boundary_class_P6S (Kh := fun n => Kh (ψ n))
        (σ := fun n => σ (ψ n)) (y := fun n => y (ψ n)) (fun n => Or.inl (h n))
        (fun n => hsel (ψ n)) n)⟩
  · exact ⟨ψ, hψ, Or.inr (Or.inr fun n =>
      not_exists_witness_of_boundary_class_P6S (Kh := fun n => Kh (ψ n))
        (σ := fun n => σ (ψ n)) (y := fun n => y (ψ n)) (fun n => Or.inr (h n))
        (fun n => hsel (ψ n)) n)⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
