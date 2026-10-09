import DifferentialGeometry.Topology.MetricSpace.VariableRadiusCover
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
open Set
namespace Metric

variable {X : Type*} [MetricSpace X]

theorem estimates_of_intersecting_lipschitz_scale_balls
    {ρ : X → ℝ} {Λ : NNReal} {Δ : ℝ} {p q : X}
    (hρ : LipschitzWith Λ ρ) (hΔ : 0 < Δ) (hq : 0 < ρ q)
    (hsmall : (Λ : ℝ) * Δ ≤ 1 / 100)
    (hinter : (ball p (Δ * ρ p / 3) ∩ ball q (Δ * ρ q / 3)).Nonempty) :
    dist p q < 7 / 10 * Δ * ρ q ∧ ρ p < 101 / 100 * ρ q := by
  obtain ⟨z, hzp, hzq⟩ := hinter
  have hd : 3 * dist p q < Δ * ρ p + Δ * ρ q := by
    have htri := dist_triangle p z q
    rw [dist_comm p z] at htri
    change dist z p < Δ * ρ p / 3 at hzp
    change dist z q < Δ * ρ q / 3 at hzq
    linarith only [htri, hzp, hzq]
  have hlip := (abs_le.mp (show |ρ p - ρ q| ≤ (Λ : ℝ) * dist p q by
    simpa only [Real.dist_eq] using hρ.dist_le_mul p q)).2
  have hdist : dist p q < 7 / 10 * Δ * ρ q := by
    have hs := mul_le_mul_of_nonneg_right hsmall (dist_nonneg (x := p) (y := q))
    have hr := mul_le_mul_of_nonneg_left hlip hΔ.le
    nlinarith only [hd, hs, hr, mul_pos hΔ hq]
  have hratio : ρ p < 101 / 100 * ρ q := by
    have hs := mul_le_mul_of_nonneg_right hsmall hq.le
    have hr := mul_le_mul_of_nonneg_left hdist.le Λ.coe_nonneg
    nlinarith only [hlip, hs, hr, hq]
  exact ⟨hdist, hratio⟩

theorem exists_finite_disjoint_lipschitz_scale_selection [CompactSpace X]
    (E : Set X) {ρ : X → ℝ} {Λ : NNReal} {Δ : ℝ}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hsmall : (Λ : ℝ) * Δ ≤ 1 / 100) :
    ∃ I : Set X, I ⊆ E ∧ I.Finite ∧ I.PairwiseDisjoint (fun i => ball i (Δ * ρ i / 3)) ∧
      ∀ p ∈ E, ∃ i ∈ I, dist p i < 7 / 10 * Δ * ρ i ∧
        ρ p < 101 / 100 * ρ i ∧ ball p (Δ * ρ p) ⊆ ball i (2 * Δ * ρ i) := by
  classical
  by_cases hX : Nonempty X
  · let := hX
    obtain ⟨pmin, _, hmin⟩ := isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hρ.continuous.continuousOn
    obtain ⟨pmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hρ.continuous.continuousOn
    obtain ⟨I, hIE, hfin, hdisj, hcover⟩ := exists_finite_disjoint_ball_selection
      (isCompact_univ.totallyBounded.subset (subset_univ E)) (fun p => Δ * ρ p / 3) (R := Δ * ρ pmax / 3)
      (show 0 < Δ * ρ pmin / 3 from div_pos (mul_pos hΔ (hρpos pmin)) (by norm_num))
      (fun p _ => by nlinarith only [mul_le_mul_of_nonneg_left (hmin (mem_univ p)) hΔ.le])
      (fun p _ => by nlinarith only [mul_le_mul_of_nonneg_left (hmax (mem_univ p)) hΔ.le])
    refine ⟨I, hIE, hfin, hdisj, ?_⟩
    intro p hp
    obtain ⟨i, hi, hinter, _⟩ := hcover p hp
    obtain ⟨hd, hr⟩ := estimates_of_intersecting_lipschitz_scale_balls hρ hΔ (hρpos i) hsmall hinter
    refine ⟨i, hi, hd, hr, ?_⟩
    intro x hx
    have htri := dist_triangle x p i
    change dist x p < Δ * ρ p at hx
    change dist x i < 2 * Δ * ρ i
    have hr' := mul_lt_mul_of_pos_left hr hΔ
    nlinarith only [htri, hx, hd, hr', mul_pos hΔ (hρpos i)]
  · exact ⟨∅, empty_subset E, finite_empty, by simp, fun p _ => (hX ⟨p⟩).elim⟩

end Metric
