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

namespace MeasureTheory

theorem norm_varying_coefficient_sum_le
    {P ι : Type*} [MeasurableSpace P] [Fintype ι] {μ : Measure P}
    (a : ι → P → ℝ) (ha : ∀ i, MemLp (a i) ∞ μ)
    (C : ι → ℝ)
    (hbound : ∀ i, ∀ᵐ p ∂μ, ‖a i p‖ ≤ C i)
    (V : ι → Lp ℝ 2 μ) (F : Lp ℝ 2 μ)
    (hF : F =ᵐ[μ] fun p => ∑ i, a i p * V i p) :
    ‖F‖ ≤ ∑ i, C i * ‖V i‖ := by
  classical
  have hmem (i : ι) : MemLp (fun p => a i p * V i p) 2 μ :=
    (Lp.memLp (V i)).mul' (ha i)
  let E : ι → Lp ℝ 2 μ := fun i => (hmem i).toLp (fun p => a i p * V i p)
  have hE (i : ι) : E i =ᵐ[μ] fun p => a i p * V i p := (hmem i).coeFn_toLp
  have hEnorm (i : ι) : ‖E i‖ ≤ C i * ‖V i‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hE i, hbound i] with p hp hbp
    rw [hp, norm_mul]
    exact mul_le_mul_of_nonneg_right hbp (norm_nonneg _)
  have hFE : F = ∑ i, E i := by
    apply Lp.ext
    have hsum : (∑ i, E i : Lp ℝ 2 μ) =ᵐ[μ] fun p => ∑ i, E i p := by
      filter_upwards [Lp.coeFn_finsetSum (Finset.univ : Finset ι) E] with p hp
      simpa only [Finset.sum_apply] using hp
    filter_upwards [hF, hsum, ae_all_iff.mpr hE] with p hFp hs hEp
    calc
      F p = ∑ i, a i p * V i p := hFp
      _ = ∑ i, E i p := Finset.sum_congr rfl (fun i _ => (hEp i).symm)
      _ = (∑ i, E i) p := hs.symm
  rw [hFE]
  calc
    ‖∑ i, E i‖ ≤ ∑ i, ‖E i‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * ‖V i‖ := Finset.sum_le_sum (fun i _ => hEnorm i)

theorem norm_double_varying_coefficient_sum_le
    {P ι κ : Type*} [MeasurableSpace P] [Fintype ι] [Fintype κ] {μ : Measure P}
    (a : ι → κ → P → ℝ) (ha : ∀ i j, MemLp (a i j) ∞ μ)
    (C : ι → κ → ℝ)
    (hbound : ∀ i j, ∀ᵐ p ∂μ, ‖a i j p‖ ≤ C i j)
    (V : ι → Lp ℝ 2 μ) (F : Lp ℝ 2 μ)
    (hF : F =ᵐ[μ] fun p => ∑ i, ∑ j, a i j p * V i p) :
    ‖F‖ ≤ ∑ i, ∑ j, C i j * ‖V i‖ := by
  classical
  have hmem (i : ι) (j : κ) : MemLp (fun p => a i j p * V i p) 2 μ :=
    (Lp.memLp (V i)).mul' (ha i j)
  let E : ι → κ → Lp ℝ 2 μ := fun i j =>
    (hmem i j).toLp (fun p => a i j p * V i p)
  have hE (i : ι) (j : κ) : E i j =ᵐ[μ] fun p => a i j p * V i p :=
    (hmem i j).coeFn_toLp
  have hEnorm (i : ι) (j : κ) : ‖E i j‖ ≤ C i j * ‖V i‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hE i j, hbound i j] with p hp hbp
    rw [hp, norm_mul]
    exact mul_le_mul_of_nonneg_right hbp (norm_nonneg _)
  have hsum : (∑ i, ∑ j, E i j : Lp ℝ 2 μ) =ᵐ[μ]
      fun p => ∑ i, ∑ j, E i j p := by
    filter_upwards [Lp.coeFn_finsetSum (Finset.univ : Finset ι)
      (fun i => ∑ j, E i j),
      ae_all_iff.mpr (fun i => Lp.coeFn_finsetSum (Finset.univ : Finset κ) (E i))]
      with p hp hpi
    rw [hp, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact (hpi i).trans (Finset.sum_apply p _ _)
  have hFE : F = ∑ i, ∑ j, E i j := by
    apply Lp.ext
    filter_upwards [hF, hsum, ae_all_iff.mpr (fun i => ae_all_iff.mpr (hE i))]
      with p hFp hs hEp
    calc
      F p = ∑ i, ∑ j, a i j p * V i p := hFp
      _ = ∑ i, ∑ j, E i j p := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (hEp i j).symm
      _ = (∑ i, ∑ j, E i j) p := hs.symm
  rw [hFE]
  calc
    ‖∑ i, ∑ j, E i j‖ ≤ ∑ i, ‖∑ j, E i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖E i j‖ := by
      exact Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, C i j * ‖V i‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hEnorm i j

end MeasureTheory
