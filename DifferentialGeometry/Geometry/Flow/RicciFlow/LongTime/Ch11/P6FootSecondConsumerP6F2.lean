import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FootSecondP6F2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDP6BT

/-!
# O-CH11-FOOT2 consumers（后缀 `_P6F2`）

`P6FootSecondP6F2.lean` 三项的消费端（都是 `example`，类型由被喂的定理推出）：
* **C-G2（HP2 元组对齐）**：HRESTP/HP2 组装 `hrestP_of_slots_P6HP2` 的 binder 原形
  `hcan₁ hdomF hηε hsmall`（`hdomF : C1₁ ≤ C1 ∧ C2₁ ≤ C2 ∧ Ctime₁ ≤ Ctime`）+ S1 + S14 ⇒
  `hceil_event_P6F2` ⇒ SCALESEP `hscaleSep_of_ceiling_P6SS` 的 `hceil` 槽，得到 `hscaleSep`（无 S11）。
* **C-G3（HB2 `hcenE` 槽）**：`hrec6S_of_supplies_P6F2` ⇒ `hcenE_of_noShortcut_sel_P6F2` ⇒
  `hbd_stage_late_P6HB2` 的 `hcenE`；剩余 binder = `hcapWL hfoot htrans hrerunE8`（逐字不变）。
* **C-G1（hfootE 全链）**：`hmargin_of_supplies_P6F2` 喂 BCDT `hlocBCD_of_supplies_P6BT` 的 `hmargin`，
  再与 C-G2 的 `hscaleSep` 经 `hBCDE_of_localBCD_P6PF` / `hfootE_of_terminalBCD_P6PF` 合成 HbdLate rev3 的
  `hfootE`；剩余 binder = BCDT 的 `hrecords hpinch hderiv hkappa`。
olean：BCDT 两文件不在 SNAP root65，INT 需先自编（Kernel → Main），再编本文件。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-- **C-G2**：HP2 的 `hcan₁ hdomF hηε hsmall` 原形 + S1 + S14 ⇒ `hscaleSep`（SCALESEP G1a 的 `hceil` 由
`hceil_event_P6F2` 付；不需要 S11 `hder`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {q : CutoffParameters} {η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0}
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hdomF : C1₁ ≤ C1 ∧ C2₁ ≤ C2 ∧ Ctime₁ ≤ Ctime) (hηε : η₁ ≤ ε) (hsmall : ε < 1 / 11)
    (hS1 : GC.LongTime.Ch11.AccuracyDecaySupply_C11S q.delta)
    (hS14 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) :=
  ObservedHistory.hscaleSep_of_ceiling_P6SS (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
    (tendsto_delta_of_accuracyDecay_P6SS q hS1)
    (ObservedHistory.hrec_of_lateRecords_P6SS (ObservedHistory.lateRecords_of_S14_P6SS hS14))
    (hceil_event_P6F2 hcan₁ hηε hsmall hdomF.1 hdomF.2.1)

/-- **C-G3**：`hrec6S`（S14 + S1 + `hcan₁` + 常数比较，无 `hcompat`）⇒ HCENP 孪生 ⇒ HB2 `hcenE` 槽。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime₁ : ℝ≥0}
    {q : CutoffParameters} (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hS14 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hηε : η₁ ≤ ε) (hC1 : C1₁ ≤ C1) (hC2 : C2₁ ≤ C2) :=
  fun hcapWL hfoot htrans hrerunE8 =>
    ObservedHistory.hbd_stage_late_P6HB2 (F := F) (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
      (C1f := C1f) (C2f := C2f) (m := m) (kk := kk) (η₁ := η₁) (C1₁ := C1₁) (C2₁ := C2₁)
      (Ctime₁ := Ctime₁) hcapWL hfoot htrans
      (hcenE_of_noShortcut_sel_P6F2 F hε hε' hCs1 hCs2
        (hrec6S_of_supplies_P6F2 hS14 hδq hcan₁ hηε hε' hC1 hC2)) hrerunE8

/-- **C-G1**：`hmargin`（G1 闭合形）喂 BCDT，`hscaleSep`（C-G2 路线）一起合成 `hfootE`；剩余 binder =
BCDT 的 `hrecords hpinch hderiv hkappa`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {C1f C2f m : ℝ} {kk : ℕ} {q : CutoffParameters}
    {η₁ C1₁ C2₁ : ℝ} {κ Cd : ℝ} {Cder Cgrad : ℝ≥0} {phi : ℝ → ℝ}
    (hε0 : 0 < ε) (hε : ε < 1 / 11) (hC1f : 1 ≤ C1f) (hC2f : 1 ≤ C2f) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hkk : max 2 ⌈ε⁻¹⌉₊ ≤ kk)
    (hεle : ε ≤ coneAccuracy) (hκ : 0 < κ) (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hCs1 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C1)
    (hCs2 : GC.LongTime.Ch11.capCollarCs_P6HE.{u} ε ≤ C2)
    (hS1 : GC.LongTime.Ch11.AccuracyDecaySupply_C11S q.delta)
    (hS14 : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hηε : η₁ ≤ ε) (hC1 : C1₁ ≤ C1) (hC2 : C2₁ ≤ C2) :=
  fun hrecords hpinch hderiv hkappa =>
    ObservedHistory.hfootE_of_terminalBCD_P6PF hε0 hε hC1f hC2f hm0 hm1 hkk
      (ObservedHistory.hBCDE_of_localBCD_P6PF
        (hlocBCD_of_supplies_P6BT (Cd := Cd) (Cder := Cder) (Cgrad := Cgrad) hεle hκ hphi
          (hmargin_of_supplies_P6F2 (Ctime := Ctime) F hε0 hε hCs1 hCs2 hS14
            (tendsto_delta_of_accuracyDecay_P6SS q hS1) hcan₁ hηε hC1 hC2)
          hrecords hpinch hderiv hkappa)
        (ObservedHistory.hscaleSep_of_ceiling_P6SS
          (tendsto_delta_of_accuracyDecay_P6SS q hS1)
          (ObservedHistory.hrec_of_lateRecords_P6SS (ObservedHistory.lateRecords_of_S14_P6SS hS14))
          (hceil_event_P6F2 hcan₁ hηε hε hC1 hC2)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
