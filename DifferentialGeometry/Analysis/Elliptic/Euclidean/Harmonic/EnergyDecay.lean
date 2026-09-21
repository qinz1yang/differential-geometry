import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Comparison
import DifferentialGeometry.Analysis.Asymptotics.PowerDecay
import DifferentialGeometry.Analysis.Asymptotics.GeometricDecay

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_weak_energy_power_bound_of_arbitrarily_small_harmonic_error
    {z : V → F} {R : ℝ}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∀ (c : V) (s : ℝ), 0 < s → ‖c‖ + s < r →
        ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (ball c s)),
          (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (ball c s) φ →
            (∫ x in ball c s, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
          (∑ i, ∫ x in ball c s, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
            δ * ∑ i, ∫ x in ball c s, ‖(hz i).weakGrad x‖ ^ 2)
    {q : ℝ} (hq : 0 < q) (hq2 : q < 2) :
    ∃ σ K : ℝ, 0 < σ ∧ σ < R ∧ 0 ≤ K ∧
      ∀ c ∈ ball (0 : V) σ, ∀ s : ℝ, 0 < s → s ≤ σ →
        (∑ i, ∫ x in ball c s, ‖(hz i).weakGrad x‖ ^ 2) ≤ K * s ^ q := by
  obtain ⟨θ, hθ, hθ4, hθsmall⟩ := Real.exists_pos_lt_mul_rpow_lt_mul_rpow
    (A := (512 : ℝ)) (p := (2 : ℝ)) (q := q) hq2
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 4)
  have hθ1 : θ < 1 := by linarith
  have hθq : 0 < θ ^ q := Real.rpow_pos_of_pos hθ q
  let δ := min 1 (θ ^ q / 4)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδq : 2 * δ ≤ θ ^ q / 2 := by
    have h := min_le_right (1 : ℝ) (θ ^ q / 4)
    dsimp only [δ]
    linarith
  have hcontract : 256 * (1 + δ) * θ ^ 2 + 2 * δ ≤ θ ^ q := by
    rw [Real.rpow_two] at hθsmall
    have h := mul_le_mul_of_nonneg_right hδ1 (sq_nonneg θ)
    nlinarith
  obtain ⟨r, hr, hrR, hcomp⟩ := happrox δ hδ
  let σ := r / 3
  have hσ : 0 < σ := div_pos hr (by norm_num)
  have hσR : σ < R := by dsimp only [σ]; linarith
  let M := ∑ i, ∫ x in ball (0 : V) R, ‖(hz i).weakGrad x‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  let K := M / (θ * σ) ^ q
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨σ, K, hσ, hσR, hK, ?_⟩
  intro c hc s hs hsσ
  have hcr : ‖c‖ + σ < r := by
    have hcn := mem_ball_zero_iff.mp hc
    dsimp only [σ] at hcn ⊢
    linarith
  have hball : ball c σ ⊆ ball (0 : V) R := by
    intro x hx
    have hn : ‖x‖ ≤ dist x c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
    exact mem_ball_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
  let En (t : ℝ) := ∑ i, ∫ x in ball c t, ‖(hz i).weakGrad x‖ ^ 2
  have hmono : MonotoneOn En (Ioc (0 : ℝ) σ) := by
    intro a ha b hb hab
    apply Finset.sum_le_sum
    intro i hi
    have hbR : ball c b ⊆ ball (0 : V) R := (ball_subset_ball hb.2).trans hball
    have hi : IntegrableOn (fun x => ‖(hz i).weakGrad x‖ ^ 2) (ball (0 : V) R) :=
      (hz i).weakGrad_memLp.norm.integrable_sq
    exact setIntegral_mono_set (hi.mono_set hbR)
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall (ball_subset_ball hab))
  have hstep (t : ℝ) (ht : 0 < t) (htσ : t ≤ σ) : En (θ * t) ≤ θ ^ q * En t := by
    have htR : ball c t ⊆ ball (0 : V) R := (ball_subset_ball htσ).trans hball
    obtain ⟨h, hh, hEuler, herr⟩ := hcomp c t ht (by linarith)
    let hzt (i : ι) := (hz i).restrict isOpen_ball htR
    have hdec := integral_weakGrad_sq_le_of_harmonic_comparison_error ht
      (mul_nonneg hθ.le ht.le) (by nlinarith : θ * t ≤ t / 4) hzt hh hEuler herr
    rw [mul_div_cancel_right₀ θ ht.ne'] at hdec
    exact hdec.trans (mul_le_mul_of_nonneg_right hcontract
      (Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _))
  have hgeom (n : ℕ) : En (θ ^ n * σ) ≤ (θ ^ q) ^ n * M := by
    have hnpos (k : ℕ) : 0 < θ ^ k * σ := mul_pos (pow_pos hθ k) hσ
    have hnle (k : ℕ) : θ ^ k * σ ≤ σ :=
      mul_le_of_le_one_left hσ.le (pow_le_one₀ hθ.le hθ1.le)
    have h := le_geom (u := fun k => En (θ ^ k * σ)) hθq.le n (fun k _ => by
      have ht := hstep (θ ^ k * σ) (hnpos k) (hnle k)
      have he : θ ^ (k + 1) * σ = θ * (θ ^ k * σ) := by rw [pow_succ]; ring
      rwa [he])
    have hbase : En σ ≤ M := by
      apply Finset.sum_le_sum
      intro i hi
      exact setIntegral_mono_set (hz i).weakGrad_memLp.norm.integrable_sq
        (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hball)
    simp only [pow_zero, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left hbase (pow_nonneg hθq.le n))
  exact DifferentialGeometry.Analysis.radius_power_bound_of_geometric_decay hθ hθ1 hσ hq.le hM
    hmono hgeom s ⟨hs, hsσ⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
