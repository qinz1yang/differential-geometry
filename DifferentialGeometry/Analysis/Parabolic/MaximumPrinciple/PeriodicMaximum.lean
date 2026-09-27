import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PeriodicComparison

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Parabolic

theorem periodic_le_of_nonpositive_maximum_derivative
    {w : ℝ → ℝ → ℝ} {M s v : ℝ} (hsv : s < v)
    (hper : ∀ x t, w (x + 1) t = w x t)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Icc 0 1 ×ˢ Icc s v))
    (hinit : ∀ x, w x s ≤ M)
    (htdiff : ∀ x t, t ∈ Ioo s v → DifferentiableAt ℝ (fun τ => w x τ) t)
    (hmax_deriv : ∀ x t, t ∈ Ioo s v → IsLocalMax (fun y => w y t) x →
      deriv (fun τ => w x τ) t ≤ 0) :
    ∀ x t, t ∈ Icc s v → w x t ≤ M := by
  have h : ∀ x t, t ∈ Icc s v → 0 ≤ M - w x t :=
    periodic_nonneg_of_nonnegative_minimum_derivative (w := fun x t => M - w x t) hsv
      (fun x t => by rw [hper x t])
      (continuousOn_const.sub hcont)
      (fun x => sub_nonneg.mpr (hinit x))
      (fun x t ht => (htdiff x t ht).const_sub M)
      (fun x t ht hmin => by
        have hmax : IsLocalMax (fun y => w y t) x := by
          filter_upwards [hmin] with y hy
          linarith
        rw [deriv_const_sub]
        linarith [hmax_deriv x t ht hmax])
  exact fun x t ht => sub_nonneg.mp (h x t ht)

theorem le_csSup_Icc_of_periodic {F : ℝ → ℝ} (hper : ∀ x, F (x + 1) = F x)
    (hcont : ContinuousOn F (Icc 0 1)) (x : ℝ) :
    F x ≤ sSup (F '' Icc 0 1) := by
  have hstep : F x = F (x - ((⌊x⌋ : ℤ) : ℝ)) := by
    have h := add_int_period (w := fun x _ => F x) (fun x t => hper x) ⌊x⌋
      (x - ((⌊x⌋ : ℤ) : ℝ)) 0
    have h5 : x - ((⌊x⌋ : ℤ) : ℝ) + ((⌊x⌋ : ℤ) : ℝ) = x := by ring
    rw [h5] at h
    exact h
  have hmem : x - ((⌊x⌋ : ℤ) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le x), by have := Int.lt_floor_add_one x; linarith⟩
  rw [hstep]
  exact le_csSup (isCompact_Icc.image_of_continuousOn hcont).bddAbove ⟨_, hmem, rfl⟩

theorem csInf_Icc_le_of_periodic {F : ℝ → ℝ} (hper : ∀ x, F (x + 1) = F x)
    (hcont : ContinuousOn F (Icc 0 1)) (x : ℝ) :
    sInf (F '' Icc 0 1) ≤ F x := by
  have hstep : F x = F (x - ((⌊x⌋ : ℤ) : ℝ)) := by
    have h := add_int_period (w := fun x _ => F x) (fun x t => hper x) ⌊x⌋
      (x - ((⌊x⌋ : ℤ) : ℝ)) 0
    have h5 : x - ((⌊x⌋ : ℤ) : ℝ) + ((⌊x⌋ : ℤ) : ℝ) = x := by ring
    rw [h5] at h
    exact h
  have hmem : x - ((⌊x⌋ : ℤ) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le x), by have := Int.lt_floor_add_one x; linarith⟩
  rw [hstep]
  exact csInf_le (isCompact_Icc.image_of_continuousOn hcont).bddBelow ⟨_, hmem, rfl⟩

end DifferentialGeometry.Analysis.Parabolic
