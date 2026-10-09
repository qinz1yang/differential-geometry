import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AncientWitnessDecoupledP6P
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterGood_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessMonotone

/-!
# P6 精度解耦：冻结 Good 常数容纳 `C(η_out)`（S-CH11-PREC G2，后缀 `_P6P`）

外审 R-C11-5 D-13 义务 (O1)："冻结的 Good 常数必须容纳 `C(η_out)`。不能只改 ε，不改或不比较
`C1, C2, Ctime`。" 本文件把 selection 冻结的 Good 数据与 G1 `ancientWitness_decoupled_P6P` 的
`C = C(ηout)` 的关系逐项列出，并给出显式 binder 形的容纳定理。

## 关系表（谁冻结、谁是自由 binder、相对 `C(ηout)` 的要求）

* `εsel`（selection 的 Good 精度 = `Hp.epsilon`，`< 1/100`、`≤ εKL70`；冻结处
  `AnalyticSurgeryProfile.epsilon` / `P4_C11E`）：要求 `ηout ≤ εsel`；`ηout := εsel` 恒可取
  （`εsel < 1/100 < 1/11`）。处理：Good 对精度**单调**（细 ⇒ 粗，同常数；`ε ≤ ε' < 1/11`）。
* `C1'`、`C2'`（selection 撇常数；冻结处 `false_of_selection_eventSlab_P6M:78`，是在 `C` 之后取的
  **自由** binder）：必须 `C ≤ C1'`、`C ≤ C2'`。处理：取 `max C1 C`、`max C2 C`，`1 ≤` 保持
  （`Hp.C1_ge_one`）。
* `Ctime'`（同上；`EnhancedSurgeryProfile_C11E.Ctime` 为其下界）：必须 `C.toNNReal ≤ Ctime'`。
  处理：取 `max Ctime C.toNNReal`。
* profile 的 `C1 C2 Ctime`（`Hp.C1/C2`、`E.Ctime`；A12′ 装配的 `∃ ε C1 C2` 可上调）：只作**下界**，
  profile 给出的 Good 经 `mono` 升到撇常数（`goodConstants_accommodate_P6P`）。
* `εin`（左侧 hwit 精度 / compactness；G1 的 binder，`εin ≤ epsW` 为绝对常数，KRoute 另加 crossing
  accuracy）：与 `C(ηout)` **无关**（`C` 不依赖 `εin`）。若 hwit 由冻结 Good 经 `monoEps` 取得，则需
  `εsel ≤ εin`、`εin < 1/11`、`εin ≤ epsW`。
* P6D 的 `C1s C2s Cs Cq Ctime`（左侧序列的自由 binder，在 `C` 之后取）：与 `C(ηout)` 无关，不需要容纳。

结论：**不能**断言"存在 `ηout` 使 `C(ηout) ≤` 给定冻结常数"——`C(ηout)` 来自 hB8 的存在性输出，树内没有
关于它随 `ηout` 变化的显式界；正确的容纳方式是**上调撇常数**到 `max(冻结, C(ηout))`
（`goodConstants_accommodate_P6P`），因为撇常数是 selection 的自由 binder，profile 常数只作下界。
这也是 D-13 的 "列出需要调整的常数并写显式 binder"：需调整的是 `C1' C2' Ctime'` 三个，`εsel` 不动。

本文件**不**生产左侧序列的完整输入（traced regions / κ / seed / pinching / `hwit` / `hderiv`），
见 G1 与 G3。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped NNReal Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness I3)

universe u

namespace ObservedHistory

/-- 单点 witness 对精度单调（细 ⇒ 粗，同常数，neck-chart 子句同步放宽）：
`SpatialCanonicalWitness.monoEps` + `capTubeHasNeckChart.mono_eps`（`α = ε`、`α' = ε'`）。 -/
theorem exists_witness_monoEps_P6P {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M}
    {eps eps' C1 C2 : ℝ} {x : M} (heps : eps ≤ eps') (hsmall : eps' < 1 / 11)
    (h : ∃ W : SpatialCanonicalWitness g eps C1 C2 x, W.capTubeHasNeckChart eps) :
    ∃ W : SpatialCanonicalWitness g eps' C1 C2 x, W.capTubeHasNeckChart eps' :=
  let ⟨W, hW⟩ := h
  ⟨W.monoEps heps hsmall, hW.mono_eps heps hsmall heps hsmall⟩

/-- Good（`HasSpatialCanonicalTimeControl`）对精度单调：`eps ≤ eps' < 1/11`，同常数
（时间导数分量不含精度）。树内只有对常数单调的 `…_mono_P6L`。 -/
theorem hasSpatialCanonicalTimeControl_monoEps_P6P {H : ObservedHistory.{u}}
    {eps eps' C1 C2 : ℝ} {Ctime : ℝ≥0} (heps : eps ≤ eps') (hsmall : eps' < 1 / 11)
    {v : Icc (0 : ℝ) H.horizon} {z : (H.stageAt v).Carrier}
    (h : H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    H.HasSpatialCanonicalTimeControl eps' C1 C2 Ctime v z := by
  obtain ⟨hw, ht⟩ := h
  exact ⟨exists_witness_monoEps_P6P heps hsmall hw, ht⟩

/-- Good 对（精度，常数）联合单调：`eps ≤ eps' < 1/11`、`C1 ≤ C1'`、`C2 ≤ C2'`、`Ctime ≤ Ctime'`。 -/
theorem hasSpatialCanonicalTimeControl_mono_all_P6P {H : ObservedHistory.{u}}
    {eps eps' C1 C2 C1' C2' : ℝ} {Ctime Ctime' : ℝ≥0} (heps : eps ≤ eps')
    (hsmall : eps' < 1 / 11) (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') (hCtime : Ctime ≤ Ctime')
    {v : Icc (0 : ℝ) H.horizon} {z : (H.stageAt v).Carrier}
    (h : H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    H.HasSpatialCanonicalTimeControl eps' C1' C2' Ctime' v z :=
  hasSpatialCanonicalTimeControl_mono_P6L hC1 hC2 hCtime
    (hasSpatialCanonicalTimeControl_monoEps_P6P heps hsmall h)

/-- **AD-good，解耦版**：selection 序列处处 `¬Good εsel C1' C2' Ctime'`；G1 给某子列 eventually
`Good ηout C C C.toNNReal`；`ηout ≤ εsel < 1/11` 且 `C ≤ C1'`、`C ≤ C2'`、`C.toNNReal ≤ Ctime'`
（D-13 (O1) 的显式 binder）⇒ `False`。`ηout = εsel` 时即 `false_of_not_good_of_eventually_good_P6L`。 -/
theorem false_of_not_good_of_eventually_good_decoupled_P6P {ηout εsel C C1' C2' : ℝ}
    {Ctime' : ℝ≥0} (hη : ηout ≤ εsel) (hsmall : εsel < 1 / 11) (hC1 : C ≤ C1') (hC2 : C ≤ C2')
    (hCt : C.toNNReal ≤ Ctime') (H : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (H n).horizon) (y : ∀ n, ((H n).stageAt (t n)).Carrier)
    (hbad : ∀ n, ¬ (H n).HasSpatialCanonicalTimeControl εsel C1' C2' Ctime' (t n) (y n))
    (hgood : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (H (ψ i)).HasSpatialCanonicalTimeControl ηout C C C.toNNReal (t (ψ i)) (y (ψ i))) :
    False := by
  obtain ⟨ψ, -, hev⟩ := hgood
  obtain ⟨i, hi⟩ := hev.exists
  exact hbad (ψ i) (hasSpatialCanonicalTimeControl_mono_all_P6P hη hsmall hC1 hC2 hCt hi)

/-- **冻结 Good 常数容纳 `C(ηout)`**（D-13 (O1)；`C` 为 G1 的 `C(ηout)`，此处任意 `1 ≤ C`）：
对冻结的 `(C1, C2, Ctime)`（profile 常数 / selection 下界）与 `ηout ≤ εsel < 1/11`，撇常数
`C1' = max C1 C`、`C2' = max C2 C`、`Ctime' = max Ctime C.toNNReal` 满足：
(i) 上调：`C1 ≤ C1'`、`C2 ≤ C2'`、`Ctime ≤ Ctime'`；(ii) 容纳：`C ≤ C1'`、`C ≤ C2'`、
`C.toNNReal ≤ Ctime'`；(iii) 保持 `1 ≤ C1'`、`1 ≤ C2'`（`Hp.C1_ge_one / C2_ge_one`）；
(iv) 冻结 Good ⇒ 撇常数 Good；(v) selection 在撇常数处的 `¬Good` 序列与 G1 的 eventual Good
（精度 `ηout`、常数 `C`）矛盾。 -/
theorem goodConstants_accommodate_P6P {C : ℝ} (hC : 1 ≤ C) (C1 C2 : ℝ) (Ctime : ℝ≥0)
    {ηout εsel : ℝ} (hη : ηout ≤ εsel) (hsmall : εsel < 1 / 11) :
    C1 ≤ max C1 C ∧ C2 ≤ max C2 C ∧ Ctime ≤ max Ctime C.toNNReal ∧
    C ≤ max C1 C ∧ C ≤ max C2 C ∧ C.toNNReal ≤ max Ctime C.toNNReal ∧
    1 ≤ max C1 C ∧ 1 ≤ max C2 C ∧
    (∀ (H : ObservedHistory.{u}) (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      H.HasSpatialCanonicalTimeControl εsel C1 C2 Ctime v z →
      H.HasSpatialCanonicalTimeControl εsel (max C1 C) (max C2 C) (max Ctime C.toNNReal) v z) ∧
    (∀ (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier),
      (∀ n, ¬ (H n).HasSpatialCanonicalTimeControl εsel (max C1 C) (max C2 C)
        (max Ctime C.toNNReal) (t n) (y n)) →
      (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
        (H (ψ i)).HasSpatialCanonicalTimeControl ηout C C C.toNNReal (t (ψ i)) (y (ψ i))) →
      False) :=
  ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_right _ _, le_max_right _ _,
    le_max_right _ _, hC.trans (le_max_right _ _), hC.trans (le_max_right _ _),
    fun _ _ _ h => hasSpatialCanonicalTimeControl_mono_P6L (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) h,
    fun H t y hbad hgood => false_of_not_good_of_eventually_good_decoupled_P6P hη hsmall
      (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) H t y hbad hgood⟩

/-- consumer：G1 的 `C(ηout)`（任意 `ηout ∈ (0, 1/11)`）喂入容纳定理——对任意冻结常数，上调后的
撇常数 `max · C(ηout)` 容纳 `C(ηout)`，且 `εsel := ηout`（`ηout ≤ εsel` 取等）时 selection 序列矛盾。 -/
example : ∃ epsW : ℝ, 0 < epsW ∧ ∀ ηout : ℝ, 0 < ηout → ηout < 1 / 11 → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (C1 C2 : ℝ) (Ctime : ℝ≥0), C ≤ max C1 C ∧ C ≤ max C2 C ∧ C.toNNReal ≤ max Ctime C.toNNReal ∧
      ∀ (H : ℕ → ObservedHistory.{0}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
        (y : ∀ n, ((H n).stageAt (t n)).Carrier),
        (∀ n, ¬ (H n).HasSpatialCanonicalTimeControl ηout (max C1 C) (max C2 C)
          (max Ctime C.toNNReal) (t n) (y n)) →
        (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
          (H (ψ i)).HasSpatialCanonicalTimeControl ηout C C C.toNNReal (t (ψ i)) (y (ψ i))) →
        False := by
  obtain ⟨epsW, hepsW, hB⟩ := ancientWitness_decoupled_P6P.{0}
  refine ⟨epsW, hepsW, fun ηout hη hs => ?_⟩
  obtain ⟨C, hC, -⟩ := hB ηout hη hs
  refine ⟨C, hC, fun C1 C2 Ctime => ?_⟩
  obtain ⟨-, -, -, h1, h2, h3, -, -, -, hfalse⟩ :=
    goodConstants_accommodate_P6P.{0} hC C1 C2 Ctime (le_refl ηout) hs
  exact ⟨h1, h2, h3, hfalse⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
