import DifferentialGeometry.Analysis.InnerProductSpace.LocalizedWeightedSpectral
import DifferentialGeometry.Analysis.Calculus.Cutoff.LocalizedNormalizedBallCutoffs
import DifferentialGeometry.Analysis.Calculus.Cutoff.NormalizedBallPartition

set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal ContDiff Topology
open Set Metric ContinuousLinearMap
namespace DifferentialGeometry.Analysis
universe u v

theorem exists_bound_normalized_ballCutoff_spectral_jets (m N : ℕ) (Λ : ℝ≥0) :
    ∃ B : ℝ≥0,
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (ι : Type v) (S : Finset ι)
        (c : ι → H) (ρ : ι → ℝ) (U : Set H),
        IsOpen U →
        (((S : Set ι) ∩ {i | (closedBall (c i) (2 * ρ i) ∩ U).Nonempty}).ncard ≤ N) →
        (∀ i ∈ S, 0 < ρ i) →
        ∀ r : ℝ, 0 < r →
        (∀ i ∈ S, (closedBall (c i) (2 * ρ i) ∩ U).Nonempty → r ≤ Λ * ρ i) →
        (∀ y ∈ U, ∃ i ∈ S, dist y (c i) ≤ ρ i) →
        ∀ (A : ι → H →L[ℝ] H),
        (∀ i ∈ S, (A i).toLinearMap.IsSymmetric) →
        ∀ (P : Submodule ℝ H) (δ : ℝ), 0 ≤ δ → δ ≤ 1 / 4 →
        (∀ i ∈ S, (closedBall (c i) (2 * ρ i) ∩ U).Nonempty →
          ‖A i - P.starProjection‖ ≤ δ) →
        let w : ι → H → ℝ := fun i y => ballCutoff (c i) (ρ i) (2 * ρ i) y /
          (∑ k ∈ S, ballCutoff (c k) (ρ k) (2 * ρ k) y)
        ∀ j ≤ m, ∀ x ∈ U,
          ‖iteratedFDeriv ℝ j (fun y =>
            (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
              Module.End.eigenspace (∑ i ∈ S, w i y • A i).toLinearMap μ).starProjection -
                P.starProjection) x‖ ≤
            max 4 ((resolventDerivativeBound 4 B j : ℝ) / 2) * δ / r ^ j := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_bound_iteratedFDeriv_normalized_ballCutoffs_of_active_card_le.{u,v} m N Λ
  refine ⟨⟨B, hB⟩, ?_⟩
  intro H _ _ _ ι S c ρ U hU hcard hρ r hr hscale hcover A hA P δ hδ hδsmall
    hclose
  classical
  dsimp only
  let w : ι → H → ℝ := fun i y => ballCutoff (c i) (ρ i) (2 * ρ i) y /
    (∑ k ∈ S, ballCutoff (c k) (ρ k) (2 * ρ k) y)
  have hw (i : ι) : ContDiffOn ℝ m (w i) U :=
    (contDiffOn_normalized_ballCutoff_of_cover S c ρ hρ hcover i).of_le (by simp)
  have hactive (i : ι) (hi : i ∈ S) (ha : ∃ y ∈ U, w i y ≠ 0) :
      (closedBall (c i) (2 * ρ i) ∩ U).Nonempty := by
    obtain ⟨y, hy, hne⟩ := ha
    refine ⟨y, ?_, hy⟩
    apply ball_subset_closedBall
    by_contra hnot
    apply hne
    change ballCutoff (c i) (ρ i) (2 * ρ i) y / _ = 0
    rw [ballCutoff_eq_zero_of_not_mem_ball (hρ i hi).le (by linarith [hρ i hi]) hnot,
      zero_div]
  intro j hj x hx
  have hD (q : ℕ) (_hq : 1 ≤ q) (hqm : q ≤ m) :
      (∑ i ∈ S, ‖iteratedFDeriv ℝ q (w i) x‖) ≤ (⟨B, hB⟩ : ℝ≥0) * (r⁻¹) ^ q := by
    simpa only [w, NNReal.coe_mk, div_eq_mul_inv, inv_pow] using
      hbound H ι S c ρ U hU hcard hρ r hr hscale hcover q hqm x hx
  have h := norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sum_smul_sub_le_of_active_close
    S hU (fun i _ => hw i)
    (fun y _ i _ => normalized_ballCutoff_nonneg S c ρ i y)
    (fun y hy => sum_normalized_ballCutoffs_eq_one_of_cover S c ρ hρ (hcover y hy))
    A hA P hδ hδsmall (inv_nonneg.mpr hr.le)
    (fun i hi ha => hclose i hi (hactive i hi ha)) hx ⟨B, hB⟩ hD j hj
  simpa only [w, div_eq_mul_inv, inv_pow] using h

end DifferentialGeometry.Analysis
