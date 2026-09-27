import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.EnergyDecay
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CampanatoGradient
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.HarmonicComparison

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_holder_bound_of_local_weak_energy_power_bound
    {z : V → F} {R q K : ℝ} (hR : 0 < R) (hq : 0 < q) (hq2 : q ≤ 2) (hK : 0 ≤ K)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hzc : ContinuousOn z (ball (0 : V) R))
    (hpower : ∀ c ∈ ball (0 : V) R, ∀ s : ℝ, 0 < s → s ≤ R →
      (∑ i, ∫ x in ball c s, ‖(hz i).weakGrad x‖ ^ 2) ≤ K * s ^ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ball (0 : V) (R / 2), ∀ y ∈ ball (0 : V) (R / 2),
      ‖z x - z y‖ ≤ C * ‖x - y‖ ^ (q / 2) := by
  apply exists_holder_bound_of_continuous_weak_gradient_power_bound hR
    (by linarith : 0 < q / 2) (by linarith : q / 2 ≤ 1) hz hzc hK
  intro b
  have hb := hpower b.center (b.subset_ball (mem_ball_self b.radius_pos))
    b.radius b.radius_pos b.radius_le
  have heq : 2 * (q / 2) = q := by ring
  simpa only [heq] using hb

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {m : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin m)

theorem exists_energy_and_holder_bounds_of_continuous_metric_minimizer
    {z : V → F} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hzc : ContinuousOn z (ball (0 : V) R)) (hz0 : z 0 = 0)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) (hB : ContinuousOn B (closedBall (0 : F) a))
    (hsym : ∀ v w, B 0 v w = B 0 w v)
    {lam : ℝ} (hlam : 0 < lam) (hcoerce : ∀ v, lam * ‖v‖ ^ 2 ≤ B 0 v v)
    (hmin : ∀ (c : V) (s : ℝ), 0 < s → ‖c‖ + s < R →
      ∀ (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball c s)),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball c s)) →
      (∀ᵐ x ∂volume.restrict (ball c s), q x ∈ closedBall (0 : F) a) →
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball c s, B (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball c s, B (q x)
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))) :
    ∃ σ K H : ℝ, 0 < σ ∧ σ < R ∧ 0 ≤ K ∧ 0 ≤ H ∧
      (∀ c ∈ ball (0 : V) σ, ∀ s : ℝ, 0 < s → s ≤ σ →
        (∑ i, ∫ x in ball c s, ‖(hz i).weakGrad x‖ ^ 2) ≤ K * s ^ ((3 : ℝ) / 2)) ∧
      ∀ x ∈ ball (0 : V) (σ / 2), ∀ y ∈ ball (0 : V) (σ / 2),
        ‖z x - z y‖ ≤ H * ‖x - y‖ ^ ((3 : ℝ) / 4) := by
  have hzc0 : ContinuousAt z 0 := hzc.continuousAt (ball_mem_nhds _ hR)
  have happ : ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∀ (c : V) (s : ℝ), 0 < s → ‖c‖ + s < r →
        ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (ball c s)),
          (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (ball c s) φ →
            (∫ x in ball c s, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
          (∑ i, ∫ x in ball c s, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
            δ * ∑ i, ∫ x in ball c s, ‖(hz i).weakGrad x‖ ^ 2 := by
    intro δ hδ
    obtain ⟨r, hr, hrR, hc⟩ :=
      exists_uniform_harmonic_comparison_error_of_continuous_metric_minimizer
        hR ha hz hzc0 hz0 B hB hsym hlam hcoerce hmin hδ
    refine ⟨r, hr, hrR, ?_⟩
    intro c s hs hcs
    obtain ⟨h, hh, _, hEuler, herr⟩ := hc c s hs hcs
    exact ⟨h, hh, hEuler, herr⟩
  obtain ⟨σ, K, hσ, hσR, hK, hpower⟩ :=
    exists_weak_energy_power_bound_of_arbitrarily_small_harmonic_error hz happ
      (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2)
  have hsub : ball (0 : V) σ ⊆ ball (0 : V) R := ball_subset_ball hσR.le
  let hzσ (i : Fin m) := (hz i).restrict isOpen_ball hsub
  obtain ⟨H, hH, hHolder⟩ := exists_holder_bound_of_local_weak_energy_power_bound hσ
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2) hK hzσ (hzc.mono hsub)
    hpower
  refine ⟨σ, K, H, hσ, hσR, hK, hH, hpower, ?_⟩
  norm_num only [show ((3 : ℝ) / 2) / 2 = 3 / 4 by norm_num] at hHolder
  exact hHolder

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
