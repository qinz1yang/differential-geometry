import DifferentialGeometry.Analysis.Calculus.Cutoff.NormalizedBallCutoffs
import Mathlib.Data.Set.Card

set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal ContDiff Topology
open Set Metric

namespace DifferentialGeometry.Analysis
universe u v

theorem exists_bound_iteratedFDeriv_normalized_ballCutoffs_of_active_card_le
    (m N : ℕ) (Λ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        (ι : Type v) (S : Finset ι) (c : ι → H) (ρ : ι → ℝ) (U : Set H),
        IsOpen U →
        (((S : Set ι) ∩ {i | (closedBall (c i) (2 * ρ i) ∩ U).Nonempty}).ncard ≤ N) →
        (∀ i ∈ S, 0 < ρ i) →
        ∀ r : ℝ, 0 < r →
        (∀ i ∈ S, (closedBall (c i) (2 * ρ i) ∩ U).Nonempty → r ≤ Λ * ρ i) →
        (∀ y ∈ U, ∃ i ∈ S, dist y (c i) ≤ ρ i) →
        ∀ j ≤ m, ∀ x ∈ U,
          (∑ i ∈ S, ‖iteratedFDeriv ℝ j
            (fun y => ballCutoff (c i) (ρ i) (2 * ρ i) y /
              (∑ k ∈ S, ballCutoff (c k) (ρ k) (2 * ρ k) y)) x‖) ≤ C / r ^ j := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_iteratedFDeriv_normalized_ballCutoffs.{u,v} m N Λ
  refine ⟨C, hC, ?_⟩
  intro H _ _ ι S c ρ U hU hcard hρ r hr hscale hcover j hjm x hx
  classical
  let J : Finset ι := S.filter (fun i => (closedBall (c i) (2 * ρ i) ∩ U).Nonempty)
  let φ : ι → H → ℝ := fun i => ballCutoff (c i) (ρ i) (2 * ρ i)
  have hJS : J ⊆ S := Finset.filter_subset _ _
  have hJset : (J : Set ι) = (S : Set ι) ∩ {i | (closedBall (c i) (2 * ρ i) ∩ U).Nonempty} := by
    ext i
    simp only [J, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
  have hJcard : J.card ≤ N := by
    rw [← Set.ncard_coe_finset J, hJset]
    exact hcard
  have hzero (i : ι) (hi : i ∈ S) (hnot : i ∉ J) (y : H) (hy : y ∈ U) : φ i y = 0 := by
    apply ballCutoff_eq_zero_of_not_mem_ball (hρ i hi).le (by linarith [hρ i hi])
    intro hball
    apply hnot
    exact Finset.mem_filter.mpr ⟨hi, y, ball_subset_closedBall hball, hy⟩
  have hden (y : H) (hy : y ∈ U) : (∑ i ∈ S, φ i y) = ∑ i ∈ J, φ i y := by
    exact (Finset.sum_subset hJS (fun i hi hnot => hzero i hi hnot y hy)).symm
  have hcoverJ (y : H) (hy : y ∈ U) : ∃ i ∈ J, dist y (c i) ≤ ρ i := by
    obtain ⟨i, hi, hdist⟩ := hcover y hy
    refine ⟨i, Finset.mem_filter.mpr ⟨hi, y, ?_, hy⟩, hdist⟩
    change dist y (c i) ≤ 2 * ρ i
    linarith [hρ i hi]
  have hlocal := hbound H ι J c ρ U hU hJcard
    (fun i hi => hρ i (hJS hi)) r hr
    (fun i hi => hscale i (hJS hi) (Finset.mem_filter.mp hi).2)
    hcoverJ j hjm x hx
  have heq (i : ι) :
      iteratedFDeriv ℝ j (fun y => φ i y / ∑ k ∈ S, φ k y) x =
        iteratedFDeriv ℝ j (fun y => φ i y / ∑ k ∈ J, φ k y) x := by
    have hf : (fun y => φ i y / ∑ k ∈ S, φ k y) =ᶠ[𝓝 x]
        (fun y => φ i y / ∑ k ∈ J, φ k y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [hden y hy]
    exact (hf.iteratedFDeriv ℝ j).eq_of_nhds
  have hout (i : ι) (hi : i ∈ S) (hnot : i ∉ J) :
      iteratedFDeriv ℝ j (fun y => φ i y / ∑ k ∈ S, φ k y) x = 0 := by
    have hf : (fun y => φ i y / ∑ k ∈ S, φ k y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [hzero i hi hnot y hy, zero_div]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using (hf.iteratedFDeriv ℝ j).eq_of_nhds
  change (∑ i ∈ S, ‖iteratedFDeriv ℝ j (fun y => φ i y / ∑ k ∈ S, φ k y) x‖) ≤ _
  calc
    _ = ∑ i ∈ J, ‖iteratedFDeriv ℝ j (fun y => φ i y / ∑ k ∈ S, φ k y) x‖ := by
      exact (Finset.sum_subset hJS (fun i hi hnot => by rw [hout i hi hnot, norm_zero])).symm
    _ = ∑ i ∈ J, ‖iteratedFDeriv ℝ j (fun y => φ i y / ∑ k ∈ J, φ k y) x‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [heq]
    _ ≤ C / r ^ j := hlocal

end DifferentialGeometry.Analysis
