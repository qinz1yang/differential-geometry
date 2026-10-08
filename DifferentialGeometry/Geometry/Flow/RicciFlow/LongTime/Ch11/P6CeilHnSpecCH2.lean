import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotFinalCwwP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCH2

set_option autoImplicit false

/-!
[CEILHN2：自 `P6CeilHnSpecCHN.lean` 机械克隆]
# CEIL-HN G1b：G9 在 `csHN / ctHN` 处的显式规格与 HN 支配（O-CH11-CEILHN，后缀 `_CHN`）

* `hnotK_final_cww_at_CH2`：G9 `hnotK_final_cww_P6HN` 的 `∃ (Ctime₀, Cs)` 换成显式 `ctHN ε / csHN ε`
  （`Classical.choose_spec`）；
* `hn_dominated_CH2`：HN ceiling 处 `csHN Γ.ε ≤ C1P6 X1HN`、`≤ C2P6 X2HN`、`ctHN Γ.ε ≤ p6CtimeHN`
  （R18 的目标不等式，经 `max` 扩展由 `le_max` 付）；
* `hn_dominated_fine_CH2`：J8 / JF8 处 `csHN ηf ≤ Cf′`、`ctHN ηf ≤ Cf′ᵗᵒᴺᴺ`，且 `Cf′ ≤ cb′`。
-/

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- G9 在显式 `ctHN ε / csHN ε` 处的规格（`Classical.choose_spec`）。 -/
theorem hnotK_final_cww_at0_CH2 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    0 < GC.LongTime.Ch11.ctHN0_CH2.{u} ε ∧ 1 ≤ GC.LongTime.Ch11.csHN0_CH2.{u} ε ∧
    ∀ C : ℝ≥0,
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
    ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, GC.LongTime.Ch11.csHN0_CH2.{u} ε ≤ C1 →
      GC.LongTime.Ch11.csHN0_CH2.{u} ε ≤ C2 →
      GC.LongTime.Ch11.ctHN0_CH2.{u} ε ≤ Ctime →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {Tn : ℕ → ℝ}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier),
      (∀ n, (K n).time (Fin.last (K n).eventCount) < (σ n : ℝ) ∧
        (σ n : ℝ) < (K n).horizon) → (∀ n, (σ n : ℝ) ≤ Tn n) →
    ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℕ → ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) → (∀ n, 0 < Q n) →
      (∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore C (Q n)
          (min ((K n).time j.succ) (Tn n))) →
      (∀ n (hK : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore
          C (Q n) (min (K n).horizon (Tn n))) →
      (∀ n i hi b, Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)) →
    ∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier), HEq (y n) yG' →
      ¬ (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) := by
  unfold GC.LongTime.Ch11.ctHN0_CH2 GC.LongTime.Ch11.csHN0_CH2
  rw [dite_eq_left ⟨hε, hε'⟩, dite_eq_left ⟨hε, hε'⟩]
  exact Classical.choose_spec (Classical.choose_spec (hnotK_final_cww_P6HN.{u} hε hε'))


/-- G9 在显式 `ctHN ε / csHN ε` 处的规格（`Classical.choose_spec`）。 -/
theorem hnotK_final_cww_at_CH2 {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    0 < GC.LongTime.Ch11.ctHN_CH2.{u} ε ∧ 1 ≤ GC.LongTime.Ch11.csHN_CH2.{u} ε ∧
    ∀ C : ℝ≥0,
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
    ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C1 →
      GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C2 →
      GC.LongTime.Ch11.ctHN_CH2.{u} ε ≤ Ctime →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {Tn : ℕ → ℝ}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier),
      (∀ n, (K n).time (Fin.last (K n).eventCount) < (σ n : ℝ) ∧
        (σ n : ℝ) < (K n).horizon) → (∀ n, (σ n : ℝ) ≤ Tn n) →
    ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℕ → ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) → (∀ n, 0 < Q n) →
      (∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore C (Q n)
          (min ((K n).time j.succ) (Tn n))) →
      (∀ n (hK : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore
          C (Q n) (min (K n).horizon (Tn n))) →
      (∀ n i hi b, Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)) →
    ∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier), HEq (y n) yG' →
      ¬ (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := hnotK_final_cww_at0_CH2.{u} hε hε'
  refine ⟨lt_of_lt_of_le h1 (GC.LongTime.Ch11.ctHN0_le_ctHN_CH2.{u} ε), h2.trans
    (GC.LongTime.Ch11.csHN0_le_csHN_CH2.{u} ε), fun C => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, a, b, c, d, e, h⟩ := h3 C
  exact ⟨Cb, Rn, ζ, δ₀, m₀, a, b, c, d, e, fun hC1 hC2 hCt =>
    h ((GC.LongTime.Ch11.csHN0_le_csHN_CH2.{u} ε).trans hC1)
      ((GC.LongTime.Ch11.csHN0_le_csHN_CH2.{u} ε).trans hC2)
      ((GC.LongTime.Ch11.ctHN0_le_ctHN_CH2.{u} ε).trans hCt)⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

open GC.GeneralFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal

/-- **R18 的目标不等式（HN ceiling 处）**：`Cs(Γ.ε) ≤ C1P6 X1HN`、`≤ C2P6 X2HN`、
`Ctime₀(Γ.ε) ≤ p6CtimeHN`。 -/
theorem hn_dominated_CH2 (Γ : ClosedBirthConstants) :
    csHN_CH2.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ∧
      csHN_CH2.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ∧
      ctHN_CH2.{u} Γ.epsilon ≤ p6CtimeHN_CH2.{u} Γ :=
  ⟨csHN_le_C1P6HN_CH2 Γ, csHN_le_C2P6HN_CH2 Γ, ctHN_le_p6CtimeHN_CH2 Γ⟩

/-- **J8 / JF8 处的 HN 支配**：精度 `ηf := p6FineEta Γ.ε`，坏点常数 `Cf′ = p6CoarseCHN ηf`：
`csHN ηf ≤ Cf′`、`ctHN ηf ≤ Cf′ᵗᵒᴺᴺ`、`Cf′ ≤ cb′ ≤ C1P6 X1HN`。 -/
theorem hn_dominated_fine_CH2 (Γ : ClosedBirthConstants) :
    csHN_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ∧
      ctHN_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
        (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ∧
      p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6BadCH2_CH2.{u} Γ ∧
      p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ :=
  ⟨csHN_le_p6CoarseCH2_CH2 _, ctHN_le_toNNReal_p6CoarseCH2_CH2 _,
    coarseHNFine_le_p6BadCH2_CH2 Γ,
    (coarseHNFine_le_p6BadCH2_CH2 Γ).trans (p6BadCH2_le_C1P6HN_CH2 Γ)⟩

/-- **HNOTRES 常数在 ceiling 内（CEILHN2 目标）**：`csHNR ε ≤ C1P6 X1HN`、`≤ C2P6 X2HN`、
`ctHNR ε ≤ p6CtimeHN`。 -/
theorem hnR_dominated_CH2 (Γ : ClosedBirthConstants) :
    csHNR_CH2.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ∧
      csHNR_CH2.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ∧
      ctHNR_CH2.{u} Γ.epsilon ≤ p6CtimeHN_CH2.{u} Γ :=
  ⟨(csHNR_le_csHN_CH2.{u} _).trans (csHN_le_C1P6HN_CH2 Γ),
    (csHNR_le_csHN_CH2.{u} _).trans (csHN_le_C2P6HN_CH2 Γ),
    (ctHNR_le_ctHN_CH2.{u} _).trans (ctHN_le_p6CtimeHN_CH2 Γ)⟩

/-- J8 / JF8 处：`csHNR ηf ≤ Cf′`、`ctHNR ηf ≤ Cf′ᵗᵒᴺᴺ`。 -/
theorem hnR_dominated_fine_CH2 (Γ : ClosedBirthConstants) :
    csHNR_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ∧
      ctHNR_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
        (p6CoarseCH2_CH2.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal :=
  ⟨(csHNR_le_csHN_CH2.{u} _).trans (csHN_le_p6CoarseCH2_CH2 _),
    (ctHNR_le_ctHN_CH2.{u} _).trans (ctHN_le_toNNReal_p6CoarseCH2_CH2 _)⟩

/-- consumer（RX 线）：ceiling 内（`C1 ≥ C1P6 X1HN` 等）hnot 合取由孪生 `DrvResE_RX_HSX_HNR` 付，
三条常数前提 `Cs ≤ C1`、`Cs ≤ C2`、`Ctime₀ ≤ Ctime` 由 ceiling 给出。 -/
theorem drvRX_HNO_at_ceiling_CH2 (Γ : ClosedBirthConstants)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h1 : C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ≤ C1) (h2 : C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ≤ C2)
    (h3 : p6CtimeHN_CH2.{u} Γ ≤ Ctime)
    (h : DrvResE_RX_HSX_HNR F q records Γ.epsilon C1 C2 Ctime T₀ Qt) :
    DrvResE_RX_HSX_HNO F q records Γ.epsilon C1 C2 Ctime T₀ Qt :=
  drvRX_HNO_at_CH2.{u} (epsilon_mem_C11GT6 Γ).1 (epsilon_mem_C11GT6 Γ).2
    ((hnR_dominated_CH2.{u} Γ).1.trans h1) ((hnR_dominated_CH2.{u} Γ).2.1.trans h2)
    ((hnR_dominated_CH2.{u} Γ).2.2.trans h3) h

/-- consumer（DJ 线）。 -/
theorem drvDJ_HNO_at_ceiling_CH2 (Γ : ClosedBirthConstants)
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} {records : CutoffRecords_C11S F q}
    {C1 C2 : ℝ} {Ctime : ℝ≥0} {T₀ Qt : ℕ → ℝ}
    (h1 : C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ ≤ C1) (h2 : C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ ≤ C2)
    (h3 : p6CtimeHN_CH2.{u} Γ ≤ Ctime)
    (h : DrvResE_DJ_HNR F q records Γ.epsilon C1 C2 Ctime T₀ Qt) :
    DrvResE_DJ_HNO F q records Γ.epsilon C1 C2 Ctime T₀ Qt :=
  drvDJ_HNO_at_CH2.{u} (epsilon_mem_C11GT6 Γ).1 (epsilon_mem_C11GT6 Γ).2
    ((hnR_dominated_CH2.{u} Γ).1.trans h1) ((hnR_dominated_CH2.{u} Γ).2.1.trans h2)
    ((hnR_dominated_CH2.{u} Γ).2.2.trans h3) h

end GC.LongTime.Ch11
