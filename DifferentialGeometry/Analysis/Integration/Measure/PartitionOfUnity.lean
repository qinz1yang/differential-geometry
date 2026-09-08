import DifferentialGeometry.Topology.PartitionOfUnity.CompactSupport
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

noncomputable section

open MeasureTheory Set

namespace PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {s : Set X}

theorem lintegral_eq_sum_fintsupportOn (ρ : PartitionOfUnity ι X s)
    (μ : Measure X) {K : Set X} (hK : IsCompact K) {f : X → ENNReal}
    (hf : AEMeasurable f μ) (hfK : Function.support f ⊆ K)
    (hfs : Function.support f ⊆ s) :
    ∫⁻ x, f x ∂μ = ∑ i ∈ ρ.fintsupportOn K hK,
      ∫⁻ x in tsupport (ρ i) ∩ K, ENNReal.ofReal (ρ i x) * f x ∂μ := by
  have hsum (x : X) : f x =
      ∑ i ∈ ρ.fintsupportOn K hK, ENNReal.ofReal (ρ i x) * f x := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero, Finset.sum_const_zero]
    · rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => ρ.nonneg i x),
        ρ.sum_fintsupportOn hK (hfK hx) (hfs hx), ENNReal.ofReal_one, one_mul]
  calc
    ∫⁻ x, f x ∂μ = ∫⁻ x, ∑ i ∈ ρ.fintsupportOn K hK,
        ENNReal.ofReal (ρ i x) * f x ∂μ := lintegral_congr hsum
    _ = ∑ i ∈ ρ.fintsupportOn K hK, ∫⁻ x, ENNReal.ofReal (ρ i x) * f x ∂μ :=
      lintegral_finsetSum' _ (fun i _ =>
        ((ENNReal.measurable_ofReal.comp (ρ i).continuous.measurable).aemeasurable).mul hf)
    _ = ∑ i ∈ ρ.fintsupportOn K hK,
        ∫⁻ x in tsupport (ρ i) ∩ K, ENNReal.ofReal (ρ i x) * f x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      refine ⟨subset_tsupport _ ?_, hfK (right_ne_zero_of_mul hx)⟩
      intro hzero
      exact (left_ne_zero_of_mul hx) (by rw [hzero, ENNReal.ofReal_zero])

end PartitionOfUnity
