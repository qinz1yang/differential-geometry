import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis

/-- A rank-one complex-linear coefficient using a coordinate of maximal norm.
The inverse is totalized at zero. No continuity of this coefficient is asserted. -/
def pairRankOneCoefficient (x w : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  if ‖x.2‖ ≤ ‖x.1‖ then
    x.1⁻¹ • (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight w
  else
    x.2⁻¹ • (ContinuousLinearMap.snd ℂ ℂ ℂ).smulRight w

@[simp]
theorem pairRankOneCoefficient_zero (w : ℂ × ℂ) :
    pairRankOneCoefficient 0 w = 0 := by
  simp [pairRankOneCoefficient]

/-- The differential inequality supplies the needed compatibility at every zero. -/
theorem pairRankOneCoefficient_apply {x w : ℂ × ℂ} {C : ℝ}
    (hbound : ‖w‖ ≤ C * ‖x‖) : pairRankOneCoefficient x w x = w := by
  by_cases hx : x = 0
  · have hw : w = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hx] using hbound)
      (norm_nonneg w))
    simp [hx, hw]
  · by_cases h : ‖x.2‖ ≤ ‖x.1‖
    · have hx₁ : x.1 ≠ 0 := by
        intro hz
        have hx₂ : x.2 = 0 := norm_eq_zero.mp
          (le_antisymm (by simpa [hz] using h) (norm_nonneg _))
        exact hx (Prod.ext hz hx₂)
      simp [pairRankOneCoefficient, h, smul_smul, hx₁]
    · have hx₂ : x.2 ≠ 0 := by
        intro hz
        exact h (by simp [hz])
      simp [pairRankOneCoefficient, h, smul_smul, hx₂]

/-- The max norm on the literal product `ℂ × ℂ` gives the same bound as the
differential inequality, including at the zero vector. -/
theorem norm_pairRankOneCoefficient_le {x w : ℂ × ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hbound : ‖w‖ ≤ C * ‖x‖) :
    ‖pairRankOneCoefficient x w‖ ≤ C := by
  by_cases hx : x = 0
  · simpa [hx] using hC
  · by_cases h : ‖x.2‖ ≤ ‖x.1‖
    · have hx₁ : x.1 ≠ 0 := by
        intro hz
        have hx₂ : x.2 = 0 := norm_eq_zero.mp
          (le_antisymm (by simpa [hz] using h) (norm_nonneg _))
        exact hx (Prod.ext hz hx₂)
      simp only [pairRankOneCoefficient, ite_eq_left h, norm_smul, norm_inv,
        ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_fst, one_mul]
      rw [← div_eq_inv_mul]
      exact (div_le_iff₀ (norm_pos_iff.mpr hx₁)).mpr
        (by simpa [Prod.norm_def, max_eq_left h] using hbound)
    · have hx₂ : x.2 ≠ 0 := by
        intro hz
        exact h (by simp [hz])
      simp only [pairRankOneCoefficient, ite_eq_right h, norm_smul, norm_inv,
        ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_snd, one_mul]
      rw [← div_eq_inv_mul]
      exact (div_le_iff₀ (norm_pos_iff.mpr hx₂)).mpr
        (by simpa [Prod.norm_def, max_eq_right (le_of_not_ge h)] using hbound)

/-- The dominant-coordinate selector and the total inverse are measurable. -/
theorem measurable_pairRankOneCoefficient {α : Type*} [MeasurableSpace α]
    {ξ w : α → ℂ × ℂ} (hξ : Measurable ξ) (hw : Measurable w) :
    Measurable (fun z => pairRankOneCoefficient (ξ z) (w z)) := by
  let L₁ := ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)
  let L₂ := ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.snd ℂ ℂ ℂ)
  exact Measurable.ite (measurableSet_le (continuous_norm.measurable.comp hξ.snd)
    (continuous_norm.measurable.comp hξ.fst))
    (hξ.fst.inv.smul (L₁.measurable.comp hw))
    (hξ.snd.inv.smul (L₂.measurable.comp hw))

/-- An actual pointwise differential inequality yields a bounded measurable
complex-linear system on any measurable domain, without deleting the zero set. -/
theorem exists_measurable_pair_coefficient {α : Type*} [MeasurableSpace α]
    {ξ w : α → ℂ × ℂ} (hξ : Measurable ξ) (hw : Measurable w)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, ‖w z‖ ≤ C * ‖ξ z‖) :
    ∃ A : α → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ),
      Measurable A ∧ (∀ z, A z (ξ z) = w z) ∧ (∀ z, ‖A z‖ ≤ C) := by
  exact ⟨fun z => pairRankOneCoefficient (ξ z) (w z),
    measurable_pairRankOneCoefficient hξ hw,
    fun z => pairRankOneCoefficient_apply (hbound z),
    fun z => norm_pairRankOneCoefficient_le hC (hbound z)⟩

/-- Local measurable data admit a globally bounded measurable coefficient by
extension by zero. The equation holds at every point of the specified domain. -/
theorem exists_measurable_pair_coefficient_on {α : Type*} [MeasurableSpace α]
    {s : Set α} (hs : MeasurableSet s) {ξ w : α → ℂ × ℂ}
    (hξ : Measurable (fun z : s => ξ z)) (hw : Measurable (fun z : s => w z))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z ∈ s, ‖w z‖ ≤ C * ‖ξ z‖) :
    ∃ A : α → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ),
      Measurable A ∧ (∀ z ∈ s, A z (ξ z) = w z) ∧
      (∀ z, ‖A z‖ ≤ C) ∧ (∀ z ∉ s, A z = 0) := by
  classical
  let A : α → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
    if z ∈ s then pairRankOneCoefficient (ξ z) (w z) else 0
  have hA : Measurable A := by
    apply measurable_of_restrict_of_restrict_compl hs
    · change Measurable (fun z : s => A (z : α))
      have heq : (fun z : s => A (z : α)) =
          (fun z : s => pairRankOneCoefficient (ξ z) (w z)) := by
        funext z
        exact ite_eq_left z.property
      rw [heq]
      exact measurable_pairRankOneCoefficient hξ hw
    · change Measurable (fun z : (sᶜ : Set α) => A (z : α))
      have heq : (fun z : (sᶜ : Set α) => A (z : α)) =
          (fun _ => (0 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) := by
        funext z
        exact ite_eq_right z.property
      rw [heq]
      exact measurable_const
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · intro z hz
    simpa [A, hz] using pairRankOneCoefficient_apply (hbound z hz)
  · intro z
    by_cases hz : z ∈ s
    · simpa [A, hz] using norm_pairRankOneCoefficient_le hC (hbound z hz)
    · simpa [A, hz] using hC
  · intro z hz
    simp [A, hz]

/-- A `C¹` pair satisfying the differential inequality on an open set admits a
bounded measurable complex-linear coefficient there. Its extension by zero is
globally measurable; the equation is pointwise, including zeros of the pair. -/
theorem exists_measurable_pair_dbar_coefficient
    {s : Set ℂ} (hs : IsOpen s) {ξ : ℂ → ℂ × ℂ}
    (hξ : ContDiffOn ℝ 1 ξ s) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ s, ‖(1 / 2 : ℂ) •
      (fderiv ℝ ξ z 1 + Complex.I • fderiv ℝ ξ z Complex.I)‖ ≤ C * ‖ξ z‖) :
    ∃ A : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ),
      Measurable A ∧
      (∀ z ∈ s, A z (ξ z) = (1 / 2 : ℂ) •
        (fderiv ℝ ξ z 1 + Complex.I • fderiv ℝ ξ z Complex.I)) ∧
      (∀ z, ‖A z‖ ≤ C) ∧ (∀ z ∉ s, A z = 0) := by
  have hD := hξ.continuousOn_fderiv_of_isOpen hs le_rfl
  have hw : ContinuousOn (fun z => (1 / 2 : ℂ) •
      (fderiv ℝ ξ z 1 + Complex.I • fderiv ℝ ξ z Complex.I)) s := by
    have h₁ : ContinuousOn (fun z => fderiv ℝ ξ z (1 : ℂ)) s :=
      hD.clm_apply continuousOn_const
    have hI : ContinuousOn (fun z => fderiv ℝ ξ z Complex.I) s :=
      hD.clm_apply continuousOn_const
    convert (continuousOn_const (c := (1 / 2 : ℂ))).smul
      (h₁.add ((continuousOn_const (c := Complex.I)).smul hI)) using 1
  exact exists_measurable_pair_coefficient_on hs.measurableSet
    hξ.continuousOn.domRestrict.measurable hw.domRestrict.measurable hC hbound

end DifferentialGeometry.Analysis
