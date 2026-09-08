import Mathlib.MeasureTheory.Function.Holder

noncomputable section
open Filter MeasureTheory
open scoped ENNReal

namespace MeasureTheory

theorem exists_lp_sum_mul_norm_sq_le
    {P ι κ : Type*} [MeasurableSpace P] [Fintype ι] [Fintype κ] {μ : Measure P}
    (a : ι → κ → P → ℝ) (ha : ∀ i j, MemLp (a i j) ∞ μ)
    (C : ι → κ → ℝ)
    (hbound : ∀ i j, ∀ᵐ p ∂μ, ‖a i j p‖ ≤ C i j)
    (V : P → ℝ) (hV : MemLp V 2 μ) :
    ∃ E : κ → Lp ℝ 2 μ,
      (∀ j, E j =ᵐ[μ] fun p => ∑ i, a i j p * V p) ∧
      ∑ j, ‖E j‖ ^ 2 ≤ (∑ j, (∑ i, C i j) ^ 2) * ‖hV.toLp V‖ ^ 2 := by
  have hmem (j) : MemLp (fun p => ∑ i, a i j p * V p) 2 μ :=
    memLp_finsetSum Finset.univ fun i _ => hV.mul (r := 2) (ha i j)
  let E : κ → Lp ℝ 2 μ := fun j => (hmem j).toLp (fun p => ∑ i, a i j p * V p)
  have hE (j) : E j =ᵐ[μ] fun p => ∑ i, a i j p * V p := (hmem j).coeFn_toLp
  have hn (j) : ‖E j‖ ≤ (∑ i, C i j) * ‖hV.toLp V‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hE j, hV.coeFn_toLp, ae_all_iff.mpr (fun i => hbound i j)] with p hp hVp hCp
    rw [hp, hVp, Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (norm_mul (a i j p) (V p)).le.trans
      (mul_le_mul_of_nonneg_right (hCp i) (norm_nonneg _))
  refine ⟨E, hE, ?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  calc
    ‖E j‖ ^ 2 ≤ ((∑ i, C i j) * ‖hV.toLp V‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hn j) 2
    _ = (∑ i, C i j) ^ 2 * ‖hV.toLp V‖ ^ 2 := mul_pow _ _ _

end MeasureTheory
