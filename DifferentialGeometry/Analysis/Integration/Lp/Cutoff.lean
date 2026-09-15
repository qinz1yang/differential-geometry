import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {X 𝕜 E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedRing 𝕜] [NormedAddCommGroup E]
  [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]

theorem MemLp.continuous_smul_of_tsupport_subset
    {Ω : Set X} {μ : Measure X} {u : X → E} {η : X → 𝕜} {p : ℝ≥0∞}
    (hu : MemLp u p (μ.restrict Ω)) (hΩ : MeasurableSet Ω)
    (hη : Continuous η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) :
    MemLp (fun x => η x • u x) p μ := by
  have hm : MemLp (fun x => η x • u x) p (μ.restrict Ω) :=
    hu.smul ((hη.memLp_top_of_hasCompactSupport hηc μ).restrict Ω)
  have hi := (memLp_indicator_iff_restrict hΩ).mpr hm
  have heq : Ω.indicator (fun x => η x • u x) = fun x => η x • u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h)), zero_smul]
  rwa [heq] at hi

end MeasureTheory
