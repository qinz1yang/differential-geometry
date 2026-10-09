import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotFinalCwwP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCHN

set_option autoImplicit false

/-!
# CEIL-HN G1b：G9 在 `csHN / ctHN` 处的显式规格与 HN 支配（O-CH11-CEILHN，后缀 `_CHN`）

* `hnotK_final_cww_at_CHN`：G9 `hnotK_final_cww_P6HN` 的 `∃ (Ctime₀, Cs)` 换成显式 `ctHN ε / csHN ε`
  （`Classical.choose_spec`）；
* `hn_dominated_CHN`：HN ceiling 处 `csHN Γ.ε ≤ C1P6 X1HN`、`≤ C2P6 X2HN`、`ctHN Γ.ε ≤ p6CtimeHN`
  （R18 的目标不等式，经 `max` 扩展由 `le_max` 付）；
* `hn_dominated_fine_CHN`：J8 / JF8 处 `csHN ηf ≤ Cf′`、`ctHN ηf ≤ Cf′ᵗᵒᴺᴺ`，且 `Cf′ ≤ cb′`。
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
theorem hnotK_final_cww_at_CHN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    0 < GC.LongTime.Ch11.ctHN_CHN.{u} ε ∧ 1 ≤ GC.LongTime.Ch11.csHN_CHN.{u} ε ∧
    ∀ C : ℝ≥0,
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∀ n, 0 < ζ n ∧ ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, 0 < δ₀ n ∧ δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
    ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, GC.LongTime.Ch11.csHN_CHN.{u} ε ≤ C1 →
      GC.LongTime.Ch11.csHN_CHN.{u} ε ≤ C2 →
      GC.LongTime.Ch11.ctHN_CHN.{u} ε ≤ Ctime →
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
  unfold GC.LongTime.Ch11.ctHN_CHN GC.LongTime.Ch11.csHN_CHN
  rw [dite_eq_left ⟨hε, hε'⟩, dite_eq_left ⟨hε, hε'⟩]
  exact Classical.choose_spec (Classical.choose_spec (hnotK_final_cww_P6HN.{u} hε hε'))

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

open GC.GeneralFlow
open scoped NNReal

/-- **R18 的目标不等式（HN ceiling 处）**：`Cs(Γ.ε) ≤ C1P6 X1HN`、`≤ C2P6 X2HN`、
`Ctime₀(Γ.ε) ≤ p6CtimeHN`。 -/
theorem hn_dominated_CHN (Γ : ClosedBirthConstants) :
    csHN_CHN.{u} Γ.epsilon ≤ C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ ∧
      csHN_CHN.{u} Γ.epsilon ≤ C2P6_C11GT6.{u} p6X2HN_CHN.{u} Γ ∧
      ctHN_CHN.{u} Γ.epsilon ≤ p6CtimeHN_CHN.{u} Γ :=
  ⟨csHN_le_C1P6HN_CHN Γ, csHN_le_C2P6HN_CHN Γ, ctHN_le_p6CtimeHN_CHN Γ⟩

/-- **J8 / JF8 处的 HN 支配**：精度 `ηf := p6FineEta Γ.ε`，坏点常数 `Cf′ = p6CoarseCHN ηf`：
`csHN ηf ≤ Cf′`、`ctHN ηf ≤ Cf′ᵗᵒᴺᴺ`、`Cf′ ≤ cb′ ≤ C1P6 X1HN`。 -/
theorem hn_dominated_fine_CHN (Γ : ClosedBirthConstants) :
    csHN_CHN.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6CoarseCHN_CHN.{u} (p6FineEta_C11GT6 Γ.epsilon) ∧
      ctHN_CHN.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤
        (p6CoarseCHN_CHN.{u} (p6FineEta_C11GT6 Γ.epsilon)).toNNReal ∧
      p6CoarseCHN_CHN.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ p6BadCHN_CHN.{u} Γ ∧
      p6CoarseCHN_CHN.{u} (p6FineEta_C11GT6 Γ.epsilon) ≤ C1P6_C11GT6.{u} p6X1HN_CHN.{u} Γ :=
  ⟨csHN_le_p6CoarseCHN_CHN _, ctHN_le_toNNReal_p6CoarseCHN_CHN _,
    coarseHNFine_le_p6BadCHN_CHN Γ,
    (coarseHNFine_le_p6BadCHN_CHN Γ).trans (p6BadCHN_le_C1P6HN_CHN Γ)⟩

end GC.LongTime.Ch11
