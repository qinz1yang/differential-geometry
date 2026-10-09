import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelBodyTruncP6KT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelPropsTruncP6KT2

/-!
# 截断 kernel：exp 形（KTRUNC1）与 ∃ 形（KTRUNC2 L2）的对齐桥（O-CH11-KTRUNC1 G1b，`_P6KT`）

KTRUNC2 L2（`P6KernelPropsTruncP6KT2`）把 J10GEN2B 的 ∃ 形 kernel Prop（P6HrestNoJ10P6JB）做了截断孪生
`NotKKernelT_P6KT2` / `FinalKernelT_P6KT2`；本车道 G1 把 HPB3 的 Body / exp 形做了截断孪生
`NotKBodyT_P6KT` / `FinalBodyT_P6KT` / `NotKKernelExpT_P6KT` / `FinalKernelExpT_P6KT`。两边截断三处逐字相同
（`{Q T₀ tK}`、终点 `min … (tK n)`、`has` 后 `hTnK`），因此 HPB3 原有的两座桥在截断形下照搬（PROVED）：
* exp ⇒ ∃（`epsW := epsW_CXOU2`、`C := p6CoarseC ε`）：`notKKernelT_P6KT2_of_expT_P6KT` / final 同；
* Body 对 `C` 反单调 + 单调落下：`notKBodyT_mono_P6KT`、`notKKernelExpT_of_le_P6KT`（final 同）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

open GC.LongTime.Ch11 (epsW_CXOU2 epsW_CXOU2_pos p6CoarseC_C11GT6)

/-- **桥 exp-T ⇒ ∃-T（PROVED，`_P6KT`）**：`NotKKernelExpT_P6KT` ⇒ KTRUNC2 `NotKKernelT_P6KT2`
（`epsW := epsW_CXOU2`、`C := p6CoarseC ε`；= HPB3 `notKKernelNoJ10_of_exp_P6HPB3` 的截断形）。 -/
theorem notKKernelT_P6KT2_of_expT_P6KT (h : NotKKernelExpT_P6KT.{u}) : NotKKernelT_P6KT2.{u} :=
  ⟨epsW_CXOU2.{u}, epsW_CXOU2_pos.{u}, fun ε hε hs hW hX hN hc =>
    ⟨p6CoarseC_C11GT6.{u} ε, GC.LongTime.Ch11.one_le_p6CoarseC_C11GT6.{u} ε,
      h ε hε hs hW hX hN hc⟩⟩

/-- **桥 exp-T ⇒ ∃-T（final，PROVED，`_P6KT`）**：`FinalKernelExpT_P6KT` ⇒ KTRUNC2
`FinalKernelT_P6KT2`。 -/
theorem finalKernelT_P6KT2_of_expT_P6KT (h : FinalKernelExpT_P6KT.{u}) : FinalKernelT_P6KT2.{u} :=
  ⟨epsW_CXOU2.{u}, epsW_CXOU2_pos.{u}, fun ε hε hs hW hX hN hc =>
    ⟨p6CoarseC_C11GT6.{u} ε, GC.LongTime.Ch11.one_le_p6CoarseC_C11GT6.{u} ε,
      h ε hε hs hW hX hN hc⟩⟩

/-- **截断 Body 对 `C` 反单调（PROVED，`_P6KT`）**：`C' ≤ C` 时 `BodyT ε C' ⇒ BodyT ε C`。 -/
theorem notKBodyT_mono_P6KT {ε C C' : ℝ} (hCC : C' ≤ C)
    (h : NotKBodyT_P6KT.{u} ε C') : NotKBodyT_P6KT.{u} ε C := by
  unfold NotKBodyT_P6KT at h ⊢
  intro C1' C2' Ctime' h1 h2 h3
  exact h (hCC.trans h1) (hCC.trans h2) ((Real.toNNReal_le_toNNReal hCC).trans h3)

/-- **截断 final Body 对 `C` 反单调（PROVED，`_P6KT`）**。 -/
theorem finalBodyT_mono_P6KT {ε C C' : ℝ} (hCC : C' ≤ C)
    (h : FinalBodyT_P6KT.{u} ε C') : FinalBodyT_P6KT.{u} ε C := by
  unfold FinalBodyT_P6KT at h ⊢
  intro C1' C2' Ctime' h1 h2 h3
  exact h (hCC.trans h1) (hCC.trans h2) ((Real.toNNReal_le_toNNReal hCC).trans h3)

/-- **单调落下（PROVED，`_P6KT`）**：每个合格 `ε` 在某 `C ≤ p6CoarseC ε` 处给截断 Body ⇒ exp-T。 -/
theorem notKKernelExpT_of_le_P6KT
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW_CXOU2.{u} →
      ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
      ∃ C : ℝ, C ≤ p6CoarseC_C11GT6.{u} ε ∧ NotKBodyT_P6KT.{u} ε C) :
    NotKKernelExpT_P6KT.{u} := by
  intro ε hε hs hW hX hN hc
  obtain ⟨C, hC, hB⟩ := h ε hε hs hW hX hN hc
  exact notKBodyT_mono_P6KT hC hB

/-- **单调落下（final，PROVED，`_P6KT`）**。 -/
theorem finalKernelExpT_of_le_P6KT
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW_CXOU2.{u} →
      ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
      ∃ C : ℝ, C ≤ p6CoarseC_C11GT6.{u} ε ∧ FinalBodyT_P6KT.{u} ε C) :
    FinalKernelExpT_P6KT.{u} := by
  intro ε hε hs hW hX hN hc
  obtain ⟨C, hC, hB⟩ := h ε hε hs hW hX hN hc
  exact finalBodyT_mono_P6KT hC hB

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
