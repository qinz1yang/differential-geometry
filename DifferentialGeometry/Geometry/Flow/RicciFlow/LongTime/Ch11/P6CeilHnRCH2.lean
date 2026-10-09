import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResDiagRXHNR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResDiagDJHNR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixProdHNF

set_option autoImplicit false

/-!
# CEILHN2 G1：`csHNR / ctHNR`（HNOTRES 的 hnot 合取所需常数）及其"在常数处"的规格

`drvRX_HNO_of_HNR` / `drvDJ_HNO_of_HNR`（HNOTRES，`_HNR`）带显式前提 `Cs ≤ C1`、`Cs ≤ C2`、
`Ctime₀ ≤ Ctime`，其 `(Ctime₀, Cs)` 是定理内 `hnotK_seq_a0_HNF` 的 obtain。本文件把它们变成**显式常数**：

* `csRX / ctRX`、`csDJ / ctDJ`：两个 `_HNO_of_HNR` 定理的 `∃ (Ctime₀, Cs)` 的 `Classical.choose`
  （`ε ∈ (0, 1/11)`，否则 `1`）；`csSeq / ctSeq`：`hnotK_seq_a0_HNF` 的 choose；
* `csHNR := max (max csRX csDJ) csSeq`，`ctHNR := max (max ctRX ctDJ) ctSeq`；
* `drvRX_HNO_at_CH2` / `drvDJ_HNO_at_CH2`（PROVED）：前提改写为 `csHNR ε ≤ C1`、`csHNR ε ≤ C2`、
  `ctHNR ε ≤ Ctime`（单调：更大的 `Cs` 蕴含 choose 处前提）。

与 HNOTRES repair 文字的差异：repair 写 `csHNR := hnotK_seq_a0_HNF 的 choose`；但两个 `_HNO_of_HNR`
定理的 choose 是其证明内部的 obtain，与该 choose 无可证关系，故这里取定理自身 `∃` 的 choose，并把
`hnotK_seq_a0_HNF` 的 choose 并入 max。无新 binder，无新 Prop。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 常数 -/

/-- `RX` 线的 `Ctime₀`（`ε ∈ (0, 1/11)` 取 `drvRX_HNO_of_HNR` 的 `∃ Ctime₀`，否则 `1`）。 -/
def ctRX_CH2 (ε : ℝ) : ℝ≥0 :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose (drvRX_HNO_of_HNR.{u} h.1 h.2)
  else 1

/-- `RX` 线的 `Cs`。 -/
def csRX_CH2 (ε : ℝ) : ℝ :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose (Classical.choose_spec (drvRX_HNO_of_HNR.{u} h.1 h.2))
  else 1

theorem one_le_csRX_CH2 (ε : ℝ) : 1 ≤ csRX_CH2.{u} ε := by
  by_cases h : 0 < ε ∧ ε < 1 / 11
  · unfold csRX_CH2
    rw [dite_eq_left h]
    exact (Classical.choose_spec
      (Classical.choose_spec (drvRX_HNO_of_HNR.{u} h.1 h.2))).2.1
  · unfold csRX_CH2
    rw [dite_eq_right h]

/-- `DJ` 线的 `Ctime₀`（`ε ∈ (0, 1/11)` 取 `drvDJ_HNO_of_HNR` 的 `∃ Ctime₀`，否则 `1`）。 -/
def ctDJ_CH2 (ε : ℝ) : ℝ≥0 :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose (drvDJ_HNO_of_HNR.{u} h.1 h.2)
  else 1

/-- `DJ` 线的 `Cs`。 -/
def csDJ_CH2 (ε : ℝ) : ℝ :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose (Classical.choose_spec (drvDJ_HNO_of_HNR.{u} h.1 h.2))
  else 1

theorem one_le_csDJ_CH2 (ε : ℝ) : 1 ≤ csDJ_CH2.{u} ε := by
  by_cases h : 0 < ε ∧ ε < 1 / 11
  · unfold csDJ_CH2
    rw [dite_eq_left h]
    exact (Classical.choose_spec
      (Classical.choose_spec (drvDJ_HNO_of_HNR.{u} h.1 h.2))).2.1
  · unfold csDJ_CH2
    rw [dite_eq_right h]

/-- `Seq` 线的 `Ctime₀`（`ε ∈ (0, 1/11)` 取 `hnotK_seq_a0_HNF` 的 `∃ Ctime₀`，否则 `1`）。 -/
def ctSeq_CH2 (ε : ℝ) : ℝ≥0 :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose (RetainedCoreHistory.hnotK_seq_a0_HNF.{u} h.1 h.2)
  else 1

/-- `Seq` 线的 `Cs`。 -/
def csSeq_CH2 (ε : ℝ) : ℝ :=
  if h : 0 < ε ∧ ε < 1 / 11 then
    Classical.choose (Classical.choose_spec (RetainedCoreHistory.hnotK_seq_a0_HNF.{u} h.1 h.2))
  else 1

theorem one_le_csSeq_CH2 (ε : ℝ) : 1 ≤ csSeq_CH2.{u} ε := by
  by_cases h : 0 < ε ∧ ε < 1 / 11
  · unfold csSeq_CH2
    rw [dite_eq_left h]
    exact (Classical.choose_spec
      (Classical.choose_spec (RetainedCoreHistory.hnotK_seq_a0_HNF.{u} h.1 h.2))).2.1
  · unfold csSeq_CH2
    rw [dite_eq_right h]

/-- hnot 合取常数（HNOTRES，`Cs`）。 -/
def csHNR_CH2 (ε : ℝ) : ℝ := max (max (csRX_CH2.{u} ε) (csDJ_CH2.{u} ε)) (csSeq_CH2.{u} ε)

/-- hnot 合取常数（HNOTRES，`Ctime₀`）。 -/
def ctHNR_CH2 (ε : ℝ) : ℝ≥0 := max (max (ctRX_CH2.{u} ε) (ctDJ_CH2.{u} ε)) (ctSeq_CH2.{u} ε)

theorem one_le_csHNR_CH2 (ε : ℝ) : 1 ≤ csHNR_CH2.{u} ε :=
  (one_le_csRX_CH2.{u} ε).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem csRX_le_csHNR_CH2 (ε : ℝ) : csRX_CH2.{u} ε ≤ csHNR_CH2.{u} ε :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem csDJ_le_csHNR_CH2 (ε : ℝ) : csDJ_CH2.{u} ε ≤ csHNR_CH2.{u} ε :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem csSeq_le_csHNR_CH2 (ε : ℝ) : csSeq_CH2.{u} ε ≤ csHNR_CH2.{u} ε := le_max_right _ _

theorem ctRX_le_ctHNR_CH2 (ε : ℝ) : ctRX_CH2.{u} ε ≤ ctHNR_CH2.{u} ε :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem ctDJ_le_ctHNR_CH2 (ε : ℝ) : ctDJ_CH2.{u} ε ≤ ctHNR_CH2.{u} ε :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem ctSeq_le_ctHNR_CH2 (ε : ℝ) : ctSeq_CH2.{u} ε ≤ ctHNR_CH2.{u} ε := le_max_right _ _

/-! ## 2. 常数处规格 -/

/-- **RX 线 hnot 合取，常数处规格（PROVED，单调）**：`drvRX_HNO_of_HNR` 的前提改为 `csHNR ε ≤ C1`、
`csHNR ε ≤ C2`、`ctHNR ε ≤ Ctime`（`csHNR ≥ csRX`、`ctHNR ≥ ctRX`）。 -/
theorem drvRX_HNO_at_CH2 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h1 : csHNR_CH2.{u} ε ≤ C1) (h2 : csHNR_CH2.{u} ε ≤ C2) (h3 : ctHNR_CH2.{u} ε ≤ Ctime)
    (h : DrvResE_RX_HSX_HNR F q records ε C1 C2 Ctime T₀ Qt) :
    DrvResE_RX_HSX_HNO F q records ε C1 C2 Ctime T₀ Qt := by
  obtain ⟨-, -, hs⟩ := Classical.choose_spec (Classical.choose_spec (drvRX_HNO_of_HNR.{u} hε hε'))
  have k1 : Classical.choose (Classical.choose_spec (drvRX_HNO_of_HNR.{u} hε hε')) ≤ C1 := by
    have e : csRX_CH2.{u} ε =
        Classical.choose (Classical.choose_spec (drvRX_HNO_of_HNR.{u} hε hε')) := by
      unfold csRX_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
    rw [← e]; exact (csRX_le_csHNR_CH2.{u} ε).trans h1
  have k2 : Classical.choose (Classical.choose_spec (drvRX_HNO_of_HNR.{u} hε hε')) ≤ C2 := by
    have e : csRX_CH2.{u} ε =
        Classical.choose (Classical.choose_spec (drvRX_HNO_of_HNR.{u} hε hε')) := by
      unfold csRX_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
    rw [← e]; exact (csRX_le_csHNR_CH2.{u} ε).trans h2
  have k3 : Classical.choose (drvRX_HNO_of_HNR.{u} hε hε') ≤ Ctime := by
    have e : ctRX_CH2.{u} ε = Classical.choose (drvRX_HNO_of_HNR.{u} hε hε') := by
      unfold ctRX_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
    rw [← e]; exact (ctRX_le_ctHNR_CH2.{u} ε).trans h3
  exact hs k1 k2 k3 h

/-- **DJ 线 hnot 合取，常数处规格（PROVED，单调）**：`drvDJ_HNO_of_HNR` 的前提改为 `csHNR ε ≤ C1`、
`csHNR ε ≤ C2`、`ctHNR ε ≤ Ctime`（`csHNR ≥ csDJ`、`ctHNR ≥ ctDJ`）。 -/
theorem drvDJ_HNO_at_CH2 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h1 : csHNR_CH2.{u} ε ≤ C1) (h2 : csHNR_CH2.{u} ε ≤ C2) (h3 : ctHNR_CH2.{u} ε ≤ Ctime)
    (h : DrvResE_DJ_HNR F q records ε C1 C2 Ctime T₀ Qt) :
    DrvResE_DJ_HNO F q records ε C1 C2 Ctime T₀ Qt := by
  obtain ⟨-, -, hs⟩ := Classical.choose_spec (Classical.choose_spec (drvDJ_HNO_of_HNR.{u} hε hε'))
  have k1 : Classical.choose (Classical.choose_spec (drvDJ_HNO_of_HNR.{u} hε hε')) ≤ C1 := by
    have e : csDJ_CH2.{u} ε =
        Classical.choose (Classical.choose_spec (drvDJ_HNO_of_HNR.{u} hε hε')) := by
      unfold csDJ_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
    rw [← e]; exact (csDJ_le_csHNR_CH2.{u} ε).trans h1
  have k2 : Classical.choose (Classical.choose_spec (drvDJ_HNO_of_HNR.{u} hε hε')) ≤ C2 := by
    have e : csDJ_CH2.{u} ε =
        Classical.choose (Classical.choose_spec (drvDJ_HNO_of_HNR.{u} hε hε')) := by
      unfold csDJ_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
    rw [← e]; exact (csDJ_le_csHNR_CH2.{u} ε).trans h2
  have k3 : Classical.choose (drvDJ_HNO_of_HNR.{u} hε hε') ≤ Ctime := by
    have e : ctDJ_CH2.{u} ε = Classical.choose (drvDJ_HNO_of_HNR.{u} hε hε') := by
      unfold ctDJ_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
    rw [← e]; exact (ctDJ_le_ctHNR_CH2.{u} ε).trans h3
  exact hs k1 k2 k3 h

end GC.LongTime.Ch11
