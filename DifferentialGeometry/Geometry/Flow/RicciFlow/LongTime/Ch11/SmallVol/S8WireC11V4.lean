import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.ProfileAlignC11V4

set_option autoImplicit false

/-!
# S-CH11-SMALLVOL4 G3：小尺度体积线接到 `hext` 的 S8 合取项（`_C11V4`）

`a12Enhanced_of_chain_C11P2` 的 `hext` 里 S8 合取项 =
`LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta)`。本文件把 Q3 入口
（G2 `smallVolWindow_of_hext_C11V4`：`hext` 数据 + K 的 wide 供给 ⇒ 每个 `A` 的 `nr := 0` window）
接成这个形状：

* `exists_stageDegreeBound_uniform_C11V4`：`N` **只依赖 `P`**（不依赖 `g`、`F`），所以 `ε₀(ε, C1, C2, N(P))`
  可以在 `pBase` 之前（`P g` 之后）确定——GAP-2 的量词次序所需（SMALLVOL3 的版本是 `F` 之后的 `∃ N`）；
* `s8_of_smallVol_C11V4`：显式前提 = Q3 入口前提（`hext` 数据 / GAP-2 `pBase.modelAccuracy ≤ ε₀` / K 的
  wide 供给）+ P6 (b)（`LargerBallCanonicalLateSupply_C11E`，留 binder）+ **`hspine`**
  （KL 84.1 "(a) ∧ (b) ⇒ (c)" 在放大因子 `A > 1` 处：`nr := 0` window + (b) ⇒ `LargerBallScalarAt_C11S`）
  ⇒ S8。`hwin` / `hD` / `N` 分别由 `hwin_of_linkedWindows_C11V3` /
  `four_transitionEnd_le_modelRadius_C11V3` / `exists_stageDegreeBound_uniform_C11V4` 给出（G2 内部）。

**诚实边界（`hspine`）**：(c) 不能由 Q3 window + (b) 在树内推出——(c) 的证明是 P6 的 E-local 收口
（坏点 selection ⇒ `Pre841Data_C11K` ⇒ `false_of_selection_*_P6M` 的反证链，design-C11-P6 L11–L13；
P6ANCH2 与 selection 车道在做）。本文件**不**证它，只把它作为单个显式 binder 暴露，且前提取最弱形
（只给 window 与 (b)；P6 车道需要的 records / pinching / canonical 数据同属 `(F, q, records)`，
可由 P6 车道往 `hspine` 的前提里加而不改本接线）。Q3 的贡献 = `hspine` 的 window 前提被 `hext` 数据全部 discharge。
-/

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **`N` 只依赖 `P`**：`initial_finite_freeFactor_bound P`（无条件）+ `retained_history_freeFactor`
（只用 `F.tower.initial n`）+ `stage_degree_of_freeFactor_ancestry`。对任意 `g`、任意 `F`、全部
`n j` 一致。 -/
theorem exists_stageDegreeBound_uniform_C11V4 (P : OrientedThreeStage.{u}) :
    ∃ N : ℕ, 0 < N ∧ ∀ {g : P.Metric} (F : GC.Interface.RawSurgery P g) (n : ℕ) (j),
      GC.GeneralFlow.StageFiniteDegreeBound ((F.tower.history n).toHistory.stage j) N := by
  obtain ⟨N, hN, hb⟩ := GC.GeneralFlow.initial_finite_freeFactor_bound P
  exact ⟨N, hN, fun F n j => GC.GeneralFlow.stage_degree_of_freeFactor_ancestry N hb
    (fun q => GC.GeneralFlow.retained_history_freeFactor (F.tower.history n)
      (F.tower.initial n) j q)⟩

/-- **S8 ⇐ 小尺度体积线 + P6 (b) + `hspine`**。`ε₀` 只依赖 `(ε, C1, C2, N(P))`（`N` 来自
`exists_stageDegreeBound_uniform_C11V4 P`），在 `g F pBase q` 之前确定。 -/
theorem s8_of_smallVol_C11V4 (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {pBase q : CutoffParameters},
      CollarWindowSupply_C11E.{u} pBase → ModelConstraintsSupply_C11E pBase εProf_C11E.{u} →
      q.modelRadius = pBase.modelRadius → q.modelOrder = pBase.modelOrder →
      q.modelAccuracy = pBase.modelAccuracy → pBase.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, LinkedWindowsSupply_C11E records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      LargerBallCanonicalLateSupply_C11E F ε C1 C2 →
      (∀ A : ℝ, 1 < A → (∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') →
        LargerBallCanonicalLateSupply_C11E F ε C1 C2 →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) →
      LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) := by
  obtain ⟨N, hN, hdeg⟩ := exists_stageDegreeBound_uniform_C11V4.{u} P
  obtain ⟨ε₀, hε₀, hE⟩ := smallVolWindow_of_hext_C11V4.{u} ε C1 C2 N hN
  refine ⟨ε₀, hε₀, ?_⟩
  intro g F pBase q hP3 hprof hrad hord hacc hacc₀ records hlink hδanti hρanti hcanon hwide hb
    hspine A hA
  exact hspine A hA (hE (zero_lt_one.trans hA) hP3 hprof hrad hord hacc hacc₀ records hlink hδanti
    hρanti hcanon (hdeg F) hwide) hb

/-- consumer：S8 ⇒ profile 字段形 `larger_ball_scalar_control`（全部 `A > 0`，`A ≤ 1` 树内），
即 `hext` 的 S8 合取项被本接线给出后下游 P6 / profile 的使用形。 -/
example (ε C1 C2 : ℝ) (P : OrientedThreeStage.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {g : P.Metric} {F : GC.Interface.RawSurgery P g} {pBase q : CutoffParameters},
      CollarWindowSupply_C11E.{u} pBase → ModelConstraintsSupply_C11E pBase εProf_C11E.{u} →
      q.modelRadius = pBase.modelRadius → q.modelOrder = pBase.modelOrder →
      q.modelAccuracy = pBase.modelAccuracy → pBase.modelAccuracy ≤ ε₀ →
      ∀ records : CutoffRecords_C11S F q, LinkedWindowsSupply_C11E records →
      AntitoneOn q.delta (Ici 0) → AntitoneOn q.neckRadius (Ici 0) →
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      LocalKappaWideSupply_C11Q F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius →
      LargerBallCanonicalLateSupply_C11E F ε C1 C2 →
      (∀ A : ℝ, 1 < A → (∃ κ'' : ℝ, 0 < κ'' ∧ LocalKappaWindowAt_P6B F (fun _ => 0) A κ'') →
        LargerBallCanonicalLateSupply_C11E F ε C1 C2 →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) →
      ∀ A : ℝ, 0 < A → LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A := by
  obtain ⟨ε₀, hε₀, hE⟩ := s8_of_smallVol_C11V4.{u} ε C1 C2 P
  refine ⟨ε₀, hε₀, ?_⟩
  intro g F pBase q hP3 hprof hrad hord hacc hacc₀ records hlink hδanti hρanti hcanon hwide hb
    hspine
  exact largerBallScalar_of_large_C11S (hE hP3 hprof hrad hord hacc hacc₀ records hlink hδanti
    hρanti hcanon hwide hb hspine)

end GC.LongTime.Ch11
