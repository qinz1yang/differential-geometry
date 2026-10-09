import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AncientWitnessP6D

/-!
# AD-good（合同 rev1 §R3，外审 R-C11-1 §Q9 9.2 / D-9.2）：selection 的 `¬Good` 与恢复定理对接（`_P6L`）

point selection（`ST/CanonicalTimeControlPointSelection:55`）返回
`¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' s y`（Good = 空间 witness ∧ 单侧时间导数界）；
O-CH11-P6D G2 `exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D` 输出某子列上
eventually 的**完整** `HasSpatialCanonicalTimeControl ε C C C.toNNReal`（常数 `C` 在序列前取）。
本文件：
* `hasSpatialCanonicalTimeControl_mono_P6L`：Good 对常数单调（`C1 ≤ C1'`、`C2 ≤ C2'`、`Ctime ≤ Ctime'`；
  witness 用 `enlargeConstants`，时间界放大系数）。
* `false_of_not_good_of_eventually_good_P6L`：预选 `C ≤ C1'`、`C ≤ C2'`、`C.toNNReal ≤ Ctime'`
  （D-9.2 的"预选 Ctime′"）时，selection 序列的 `¬Good` 与 P6D 的 eventual Good 矛盾。
* consumer：P6D G2 的结论 (ii) 原样喂入（型对齐）。
P6D 的 trace-local 前提（traced region、κ、pinching、witness、时间导数）的供给不在此层（见 G5 example 与
state HANDOVER：P6A L9–L11）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- Good（`HasSpatialCanonicalTimeControl`）对常数单调。 -/
theorem hasSpatialCanonicalTimeControl_mono_P6L {H : ObservedHistory.{u}} {eps C1 C2 C1' C2' : ℝ}
    {Ctime Ctime' : ℝ≥0} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') (hCtime : Ctime ≤ Ctime')
    {v : Icc (0 : ℝ) H.horizon} {z : (H.stageAt v).Carrier}
    (h : H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z) :
    H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  obtain ⟨⟨W, hW⟩, ht⟩ := h
  refine ⟨⟨W.enlargeConstants hC1 hC2, hW.enlarge_constants hC1 hC2⟩, fun hage htop => ?_⟩
  exact (ht hage htop).trans
    (mul_le_mul_of_nonneg_right (show (Ctime : ℝ) ≤ Ctime' from hCtime) (sq_nonneg _))

/-- **AD-good**：selection 序列处处 `¬Good(C1', C2', Ctime')`，恢复定理给某子列 eventually
`Good(C, C, C.toNNReal)`，且常数预选 `C ≤ C1'`、`C ≤ C2'`、`C.toNNReal ≤ Ctime'` ⇒ `False`。 -/
theorem false_of_not_good_of_eventually_good_P6L {eps C C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (hC1 : C ≤ C1') (hC2 : C ≤ C2') (hCt : C.toNNReal ≤ Ctime')
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier)
    (hbad : ∀ n, ¬ (H n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (t n) (y n))
    (hgood : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (H (ψ i)).HasSpatialCanonicalTimeControl eps C C C.toNNReal (t (ψ i)) (y (ψ i))) :
    False := by
  obtain ⟨ψ, -, hev⟩ := hgood
  obtain ⟨i, hi⟩ := hev.exists
  exact hbad (ψ i) (hasSpatialCanonicalTimeControl_mono_P6L hC1 hC2 hCt hi)

/-- consumer（型对齐）：P6D G2 结论的第二分量（eventual 完整 Good）直接喂 AD-good；
selection 常数取 `C1' = C2' = C`、`Ctime' = C.toNNReal`（预选，D-9.2）。 -/
example : ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H : ℕ → ObservedHistory.{0}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
      (y : ∀ n, ((H n).stageAt (t n)).Carrier),
      (∀ n, ¬ (H n).HasSpatialCanonicalTimeControl ε C C C.toNNReal (t n) (y n)) →
      (∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
        (H (ψ i)).HasSpatialCanonicalTimeControl ε C C C.toNNReal (t (ψ i)) (y (ψ i))) →
      False := by
  obtain ⟨epsW, hepsW, hB⟩ :=
    exists_eventually_hasSpatialCanonicalTimeControl_of_traced_seed_P6D.{0}
  refine ⟨epsW, hepsW, fun ε hε hs hεW => ?_⟩
  obtain ⟨C, hC, -⟩ := hB ε hε hs hεW
  exact ⟨C, hC, fun H t y hbad hgood =>
    false_of_not_good_of_eventually_good_P6L le_rfl le_rfl le_rfl H t y hbad hgood⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
