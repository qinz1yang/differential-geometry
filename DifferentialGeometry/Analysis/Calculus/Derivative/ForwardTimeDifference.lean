import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace DifferentialGeometry.Analysis

private theorem forward_slope_error_le
    (f f' : ℝ → ℝ) (τ M : ℝ) (hM : 0 ≤ M)
    (hc : ContinuousOn f (Icc 0 τ))
    (hd : ∀ r ∈ Ico 0 τ, HasDerivWithinAt f (f' r) (Ici 0) r)
    (hlip : ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, |f' s - f' t| ≤ M * |s - t|)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hah : a + h ≤ τ) :
    |f' a - (f (a + h) - f a) / h| ≤ M * h := by
  let F : ℝ → ℝ := fun r => f r - f a - (r - a) * f' a
  have haτ : a ≤ τ := by linarith
  have hsub : Icc a (a + h) ⊆ Icc 0 τ := by
    intro r hr
    exact ⟨ha.trans hr.1, hr.2.trans hah⟩
  have hFc : ContinuousOn F (Icc a (a + h)) :=
    ((hc.mono hsub).sub continuousOn_const).sub
      ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
  have hFd (r : ℝ) (hr : r ∈ Ico a (a + h)) :
      HasDerivWithinAt F (f' r - f' a) (Ici r) r := by
    have hr0 : 0 ≤ r := ha.trans hr.1
    have hrτ : r < τ := hr.2.trans_le hah
    have hfr := (hd r ⟨hr0, hrτ⟩).mono (fun z hz => hr0.trans hz)
    have hlin : HasDerivWithinAt (fun z : ℝ => (z - a) * f' a) (f' a) (Ici r) r := by
      exact ((((hasDerivAt_id r).sub_const a).mul_const (f' a)).congr_deriv
        (by ring)).hasDerivWithinAt
    exact (hfr.sub_const (f a)).sub hlin
  have hFb (r : ℝ) (hr : r ∈ Ico a (a + h)) : ‖f' r - f' a‖ ≤ M * h := by
    rw [Real.norm_eq_abs]
    have hl := hlip r ⟨ha.trans hr.1, hr.2.le.trans hah⟩ a ⟨ha, haτ⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (by linarith only [hr.2] : r - a ≤ h) hM)
  have hraw := norm_image_sub_le_of_norm_deriv_right_le_segment hFc hFd hFb
    (a + h) ⟨by linarith, le_rfl⟩
  have hrem : |f (a + h) - f a - h * f' a| ≤ (M * h) * h := by
    simpa only [F, sub_self, zero_mul, sub_zero, add_sub_cancel_left, Real.norm_eq_abs] using hraw
  have he : f' a - (f (a + h) - f a) / h =
      -((f (a + h) - f a - h * f' a) / h) := by
    field_simp [hh.ne']
    ring
  rw [he, abs_neg, abs_div, abs_of_pos hh]
  exact (div_le_iff₀ hh).mpr hrem

theorem right_derivative_error_le_of_value_error
    (f f' g g' : ℝ → ℝ) (τ M η : ℝ) (hM : 0 ≤ M)
    (hfc : ContinuousOn f (Icc 0 τ)) (hgc : ContinuousOn g (Icc 0 τ))
    (hfd : ∀ r ∈ Ico 0 τ, HasDerivWithinAt f (f' r) (Ici 0) r)
    (hgd : ∀ r ∈ Ico 0 τ, HasDerivWithinAt g (g' r) (Ici 0) r)
    (hfl : ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, |f' s - f' t| ≤ M * |s - t|)
    (hgl : ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, |g' s - g' t| ≤ M * |s - t|)
    (hval : ∀ r ∈ Icc 0 τ, |f r - g r| ≤ η)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 < h) (hah : a + h ≤ τ) :
    |f' a - g' a| ≤ 2 * M * h + 2 * η / h := by
  have hf := forward_slope_error_le f f' τ M hM hfc hfd hfl a h ha hh hah
  have hg := forward_slope_error_le g g' τ M hM hgc hgd hgl a h ha hh hah
  let sf : ℝ := (f (a + h) - f a) / h
  let sg : ℝ := (g (a + h) - g a) / h
  have hmid : |sf - sg| ≤ 2 * η / h := by
    have haτ : a ≤ τ := by linarith
    have hnum : |(f (a + h) - f a) - (g (a + h) - g a)| ≤ 2 * η := by
      calc |(f (a + h) - f a) - (g (a + h) - g a)|
          = |(f (a + h) - g (a + h)) - (f a - g a)| := by congr 1; ring
        _ ≤ |f (a + h) - g (a + h)| + |f a - g a| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (f (a + h) - g (a + h)) 0 (f a - g a))
        _ ≤ η + η := add_le_add (hval (a + h) ⟨by linarith, hah⟩) (hval a ⟨ha, haτ⟩)
        _ = 2 * η := by ring
    change |(f (a + h) - f a) / h - (g (a + h) - g a) / h| ≤ _
    rw [← sub_div, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hnum hh.le
  have hg' : |sg - g' a| ≤ M * h := by
    simpa only [sg, abs_sub_comm] using hg
  calc |f' a - g' a|
      ≤ |f' a - sf| + |sf - g' a| := abs_sub_le _ _ _
    _ ≤ M * h + (|sf - sg| + |sg - g' a|) :=
      add_le_add hf (abs_sub_le _ _ _)
    _ ≤ M * h + (2 * η / h + M * h) := add_le_add le_rfl (add_le_add hmid hg')
    _ = 2 * M * h + 2 * η / h := by ring

theorem uniform_right_derivative_convergence_of_uniform_convergence
    {ι : Type*} (F F' : ℕ → ι → ℝ → ℝ) (g g' : ι → ℝ → ℝ)
    (τ θ M : ℝ) (hθτ : θ < τ) (hM : 0 ≤ M) (kReg : ℕ)
    (hFc : ∀ k ≥ kReg, ∀ x, ContinuousOn (F k x) (Icc 0 τ))
    (hgc : ∀ x, ContinuousOn (g x) (Icc 0 τ))
    (hFd : ∀ k ≥ kReg, ∀ x, ∀ r ∈ Ico 0 τ,
      HasDerivWithinAt (F k x) (F' k x r) (Ici 0) r)
    (hgd : ∀ x, ∀ r ∈ Ico 0 τ, HasDerivWithinAt (g x) (g' x r) (Ici 0) r)
    (hFl : ∀ k ≥ kReg, ∀ x, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ,
      |F' k x s - F' k x t| ≤ M * |s - t|)
    (hgl : ∀ x, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ,
      |g' x s - g' x t| ≤ M * |s - t|)
    (hconv : ∀ η : ℝ, 0 < η → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ x,
      ∀ t ∈ Icc 0 τ, |F k x t - g x t| < η) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ x,
      ∀ t ∈ Icc 0 θ, |F' k x t - g' x t| < ε := by
  intro ε hε
  let h : ℝ := min ((τ - θ) / 2) (ε / (8 * (M + 1)))
  have hden : 0 < 8 * (M + 1) := by positivity
  have hh : 0 < h := lt_min (by positivity) (div_pos hε hden)
  have hmargin : h ≤ (τ - θ) / 2 := min_le_left _ _
  have hsmall : h ≤ ε / (8 * (M + 1)) := min_le_right _ _
  have hMh : 2 * M * h ≤ ε / 4 := by
    have hm := (le_div_iff₀ hden).mp hsmall
    nlinarith
  let η : ℝ := ε * h / 8
  have hη : 0 < η := by positivity
  obtain ⟨kc, hkc⟩ := hconv η hη
  refine ⟨max kc kReg, ?_⟩
  intro k hk x t ht
  have hkconv : kc ≤ k := (le_max_left kc kReg).trans hk
  have hkreg : kReg ≤ k := (le_max_right kc kReg).trans hk
  have hforward : t + h ≤ τ := by linarith [ht.2]
  have he := right_derivative_error_le_of_value_error
    (F k x) (F' k x) (g x) (g' x) τ M η hM (hFc k hkreg x) (hgc x)
    (hFd k hkreg x) (hgd x) (hFl k hkreg x) (hgl x)
    (fun r hr => (hkc k hkconv x r hr).le) t h ht.1 hh hforward
  have hcancel : 2 * η / h = ε / 4 := by
    dsimp only [η]
    field_simp [hh.ne']
    ring
  rw [hcancel] at he
  exact he.trans_lt (by linarith)

end DifferentialGeometry.Analysis

end
