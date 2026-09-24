import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicMaximum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic

theorem periodic_le_exp_of_maximum_deriv_le_mul
    {w : ℝ → ℝ → ℝ} {M C s v : ℝ} (hsv : s < v)
    (hper : ∀ x t, w (x + 1) t = w x t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, w x s ≤ M)
    (htdiff : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => w x τ) t)
    (hmax : ∀ x t, t ∈ Ioo s v → IsLocalMax (fun y => w y t) x →
      deriv (fun τ => w x τ) t ≤ C * w x t) :
    ∀ x t, t ∈ Icc s v → w x t ≤ M * Real.exp (C * (t - s)) := by
  let z : ℝ → ℝ → ℝ := fun x t => Real.exp (-C * (t - s)) * w x t
  have hdE (t : ℝ) : HasDerivAt (fun τ => Real.exp (-C * (τ - s)))
      (Real.exp (-C * (t - s)) * (-C)) t := by
    simpa using (((hasDerivAt_id t).sub_const s).const_mul (-C)).exp
  have hz : ∀ x t, t ∈ Icc s v → z x t ≤ M := by
    apply periodic_le_of_nonpositive_maximum_derivative hsv
    · intro x t
      dsimp only [z]
      rw [hper]
    · exact (Continuous.continuousOn (by fun_prop)).mul hcont
    · intro x
      simpa [z] using hinit x
    · intro x t ht
      exact (hdE t).differentiableAt.mul (htdiff x t ht)
    · intro x t ht hzmax
      have hwmax : IsLocalMax (fun y => w y t) x := by
        filter_upwards [hzmax] with y hy
        exact (mul_le_mul_iff_right₀ (Real.exp_pos (-C * (t - s)))).mp (by
          simpa only [z, mul_comm] using hy)
      have hd := (hdE t).mul (htdiff x t ht).hasDerivAt
      change deriv ((fun τ => Real.exp (-C * (τ - s))) * (fun τ => w x τ)) t ≤ 0
      rw [hd.deriv]
      have h := mul_le_mul_of_nonneg_left (hmax x t ht hwmax)
        (Real.exp_pos (-C * (t - s))).le
      nlinarith
  intro x t ht
  have h := mul_le_mul_of_nonneg_left (hz x t ht) (Real.exp_pos (C * (t - s))).le
  have hE : Real.exp (C * (t - s)) * Real.exp (-C * (t - s)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  dsimp only [z] at h
  rw [← mul_assoc, hE, one_mul] at h
  simpa only [mul_comm] using h

theorem periodic_eq_zero_of_nonnegative_of_maximum_deriv_le_mul
    {w : ℝ → ℝ → ℝ} {C s v : ℝ} (hsv : s < v)
    (hper : ∀ x t, w (x + 1) t = w x t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, w x s = 0)
    (hnonneg : ∀ x t, t ∈ Icc s v → 0 ≤ w x t)
    (htdiff : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => w x τ) t)
    (hmax : ∀ x t, t ∈ Ioo s v → IsLocalMax (fun y => w y t) x →
      deriv (fun τ => w x τ) t ≤ C * w x t) :
    ∀ x t, t ∈ Icc s v → w x t = 0 := by
  have h := periodic_le_exp_of_maximum_deriv_le_mul (M := 0) hsv hper hcont
    (fun x => (hinit x).le) htdiff hmax
  intro x t ht
  exact le_antisymm (by simpa using h x t ht) (hnonneg x t ht)

end DifferentialGeometry.Analysis.Parabolic
