import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open scoped BigOperators ContDiff
namespace DifferentialGeometry.Analysis
variable {H ι : Type*} [NormedAddCommGroup H]

theorem one_le_sum_ballCutoffs_of_cover (S : Finset ι) (c : ι → H) (ρ : ι → ℝ)
    (hρ : ∀ i ∈ S, 0 < ρ i) {x : H}
    (hcover : ∃ i ∈ S, dist x (c i) ≤ ρ i) :
    1 ≤ ∑ i ∈ S, ballCutoff (c i) (ρ i) (2 * ρ i) x := by
  classical
  obtain ⟨i, hi, hdist⟩ := hcover
  have hone : ballCutoff (c i) (ρ i) (2 * ρ i) x = 1 :=
    ballCutoff_eq_one_of_mem_closedBall (hρ i hi).le (by linarith [hρ i hi]) hdist
  rw [← hone]
  exact Finset.single_le_sum (fun k _ => (ballCutoff_mem_Icc (c k) (ρ k) (2 * ρ k) x).1) hi

theorem contDiffOn_normalized_ballCutoff_of_cover [InnerProductSpace ℝ H] (S : Finset ι) (c : ι → H) (ρ : ι → ℝ)
    (hρ : ∀ i ∈ S, 0 < ρ i) {U : Set H}
    (hcover : ∀ x ∈ U, ∃ i ∈ S, dist x (c i) ≤ ρ i) (i : ι) :
    ContDiffOn ℝ ∞ (fun x => ballCutoff (c i) (ρ i) (2 * ρ i) x /
      (∑ k ∈ S, ballCutoff (c k) (ρ k) (2 * ρ k) x)) U := by
  classical
  apply (ballCutoff_contDiff (c i) (ρ i) (2 * ρ i)).contDiffOn.div
    (ContDiffOn.sum (fun k _ => (ballCutoff_contDiff (c k) (ρ k) (2 * ρ k)).contDiffOn))
  intro x hx
  exact (lt_of_lt_of_le zero_lt_one (one_le_sum_ballCutoffs_of_cover S c ρ hρ (hcover x hx))).ne'

theorem normalized_ballCutoff_nonneg (S : Finset ι) (c : ι → H) (ρ : ι → ℝ) (i : ι) (x : H) :
    0 ≤ ballCutoff (c i) (ρ i) (2 * ρ i) x /
      (∑ k ∈ S, ballCutoff (c k) (ρ k) (2 * ρ k) x) := by
  classical
  apply div_nonneg (ballCutoff_mem_Icc (c i) (ρ i) (2 * ρ i) x).1
  exact Finset.sum_nonneg (fun k _ => (ballCutoff_mem_Icc (c k) (ρ k) (2 * ρ k) x).1)

theorem sum_normalized_ballCutoffs_eq_one_of_cover (S : Finset ι) (c : ι → H) (ρ : ι → ℝ)
    (hρ : ∀ i ∈ S, 0 < ρ i) {x : H}
    (hcover : ∃ i ∈ S, dist x (c i) ≤ ρ i) :
    (∑ i ∈ S, ballCutoff (c i) (ρ i) (2 * ρ i) x /
      (∑ k ∈ S, ballCutoff (c k) (ρ k) (2 * ρ k) x)) = 1 := by
  classical
  rw [← Finset.sum_div]
  exact div_self (lt_of_lt_of_le zero_lt_one (one_le_sum_ballCutoffs_of_cover S c ρ hρ hcover)).ne'

end DifferentialGeometry.Analysis
