import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Set



noncomputable section

open Set MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis



theorem integral_annulus_eq_polar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {r R : ℝ} (hr : 0 < r) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f z) =
      ∫ p in Icc (r, -Real.pi) (R, Real.pi),
        p.1 • f (Complex.polarCoord.symm p) := by
  let A : Set ℂ := {z | ‖z‖ ∈ Icc r R}
  let B : Set (ℝ × ℝ) := Icc r R ×ˢ (univ : Set ℝ)
  have hA : MeasurableSet A := measurableSet_Icc.preimage continuous_norm.measurable
  have hB : MeasurableSet B := measurableSet_Icc.prod MeasurableSet.univ
  rw [← integral_indicator hA, ← Complex.integral_comp_polarCoord_symm]
  have heq : (∫ p in polarCoord.target, p.1 • A.indicator f (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, B.indicator
        (fun p => p.1 • f (Complex.polarCoord.symm p)) p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hp₀ : 0 < p.1 := hp.1
    have he : Complex.polarCoord.symm p ∈ A ↔ p ∈ B := by
      simp [A, B, abs_of_pos hp₀]
    by_cases h : p ∈ B
    · simp only [indicator_of_mem (he.mpr h), indicator_of_mem h]
    · simp only [indicator_of_notMem (mt he.mp h), indicator_of_notMem h, smul_zero]
  rw [heq, setIntegral_indicator hB]
  have hset : polarCoord.target ∩ B = Icc r R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target, B, mem_inter_iff, mem_prod, mem_Ioi, mem_Icc,
      mem_univ, and_true, mem_Ioo]
    constructor
    · rintro ⟨⟨_, hθ⟩, hp⟩
      exact ⟨hp, hθ⟩
    · rintro ⟨hp, hθ⟩
      exact ⟨⟨hr.trans_le hp.1, hθ⟩, hp⟩
  rw [hset, ← Icc_prod_Icc]
  apply setIntegral_congr_set
  exact Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    (Ioo_ae_eq_Icc (α := ℝ) (μ := volume))

end DifferentialGeometry.Analysis
