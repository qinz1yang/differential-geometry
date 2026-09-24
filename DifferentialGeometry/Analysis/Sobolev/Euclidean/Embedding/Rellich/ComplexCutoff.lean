import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.LipschitzCutoff
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic

section

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

theorem rellich_kondrachov_seq_complex_cutoff_of_lipschitz
    {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηball : tsupport η ⊆ ball (0 : ℂ) 1)
    (f : ℕ → ℂ → ℝ) (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    {A B : ℝ} (hA : ∀ n, (∫ z in ball (0 : ℂ) 1, f n z ^ 2) ≤ A)
    (hB : ∀ n, (∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin 2) → ℝ),
      StrictMono φ ∧ MemLp v 2 (volume.restrict (ball 0 1)) ∧
      Tendsto (fun n => eLpNorm (fun x => η (e x) * f (φ n) (e x) - v x)
        2 (volume.restrict (ball 0 1))) atTop (𝓝 0) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let u : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ := fun n x => η (e x) * f n (e x)
  obtain ⟨C, hC, hcut⟩ := exists_memW01p_complex_cutoff_bounds_of_lipschitz hη hηc hηball
  let D := C * (Real.sqrt A + Real.sqrt B)
  have hD : 0 ≤ D := mul_nonneg hC (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hu (n : ℕ) :
      DeGiorgi.MemW01p 2 (u n) (ball 0 1) ∧
      eLpNorm (u n) 2 (volume.restrict (ball 0 1)) ≤ ENNReal.ofReal D ∧
      ∀ hw : DeGiorgi.MemW1pWitness 2 (u n) (ball 0 1), ∀ i : Fin 2,
        eLpNorm (fun x => hw.weakGrad x i) 2 (volume.restrict (ball 0 1)) ≤
          ENNReal.ofReal D := by
    obtain ⟨K, hK⟩ := hf n
    exact hcut hK (hA n) (hB n)
  have hmem (n : ℕ) : DeGiorgi.MemW01p 2 (u n) (ball 0 1) := (hu n).1
  have hfun (n : ℕ) :
      eLpNorm (u n) 2 (volume.restrict (ball 0 1)) ≤ ENNReal.ofReal (2 * D) :=
    (hu n).2.1.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  have hgrad (n : ℕ) :
      ∑ i : Fin 2,
        eLpNorm (fun x => (Classical.choose (hmem n).2).weakGrad x i)
          2 (volume.restrict (ball 0 1)) ≤ ENNReal.ofReal (2 * D) := by
    calc
      _ ≤ ∑ _i : Fin 2, ENNReal.ofReal D :=
        Finset.sum_le_sum fun i _ => (hu n).2.2 (Classical.choose (hmem n).2) i
      _ = _ := by
        simp only [Fin.sum_univ_two]
        rw [two_mul, ENNReal.ofReal_add hD hD]
  obtain ⟨φ, hφ, v, hv, hlim⟩ := rellich_kondrachov_W01p_seq
    isOpen_ball isBounded_ball (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmem hfun hgrad
  exact ⟨φ, v, hφ, hv, hlim⟩

end DifferentialGeometry.Analysis.Sobolev

end

end
