import DifferentialGeometry.Topology.PartitionOfUnity.CompactSupport
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem integrable_iff_fintsupportOn (ρ : PartitionOfUnity ι X s)
    (μ : Measure X) {K : Set X} (hK : IsCompact K) {f : X → A}
    (hfK : Function.support f ⊆ K) (hfs : Function.support f ⊆ s) :
    Integrable f μ ↔ ∀ i ∈ ρ.fintsupportOn K hK,
      IntegrableOn (fun x => ρ i x • f x) (tsupport (ρ i) ∩ K) μ := by
  constructor
  · intro hf i _
    exact (hf.bdd_smul 1 (ρ i).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (ρ.nonneg i x)]
        exact ρ.le_one i x)).integrableOn
  · intro h
    have hi (i : ι) (hi : i ∈ ρ.fintsupportOn K hK) :
        Integrable (fun x => ρ i x • f x) μ := by
      exact (integrableOn_iff_integrable_of_support_subset
        (subset_inter ((Function.support_smul_subset_left (ρ i) f).trans (subset_tsupport _))
          ((Function.support_smul_subset_right (ρ i) f).trans hfK))).mp (h i hi)
    have hsum := integrable_finsetSum (ρ.fintsupportOn K hK) hi
    simpa only [ρ.sum_fintsupportOn_smul hK hfK hfs] using hsum

theorem integral_eq_sum_fintsupportOn (ρ : PartitionOfUnity ι X s)
    (μ : Measure X) {K : Set X} (hK : IsCompact K) {f : X → A}
    (hf : Integrable f μ) (hfK : Function.support f ⊆ K)
    (hfs : Function.support f ⊆ s) :
    ∫ x, f x ∂μ = ∑ i ∈ ρ.fintsupportOn K hK,
      ∫ x in tsupport (ρ i) ∩ K, ρ i x • f x ∂μ := by
  calc
    ∫ x, f x ∂μ = ∫ x, ∑ i ∈ ρ.fintsupportOn K hK, ρ i x • f x ∂μ := by
      simp only [ρ.sum_fintsupportOn_smul hK hfK hfs]
    _ = ∑ i ∈ ρ.fintsupportOn K hK, ∫ x, ρ i x • f x ∂μ := by
      apply integral_finsetSum
      intro i _
      exact hf.bdd_smul 1 (ρ i).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (ρ.nonneg i x)]
          exact ρ.le_one i x)
    _ = ∑ i ∈ ρ.fintsupportOn K hK,
        ∫ x in tsupport (ρ i) ∩ K, ρ i x • f x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      exact Function.support_subset_iff'.mp
        (subset_inter ((Function.support_smul_subset_left (ρ i) f).trans (subset_tsupport _))
          ((Function.support_smul_subset_right (ρ i) f).trans hfK))

end PartitionOfUnity
