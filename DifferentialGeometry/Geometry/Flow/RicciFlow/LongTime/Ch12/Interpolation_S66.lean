import Mathlib

set_option autoImplicit false

/-!
# CH12-S66: Landau–Kolmogorov interpolation (pure real analysis)

* G1 `landau_1d_S66`: on `Icc a b` (length `ℓ = b - a`), `‖f'‖ ≤ 4 (√(M0 M2) + M0 / ℓ)` where
  `‖f‖ ≤ M0`, `‖f''‖ ≤ M2` (vector-valued, hypotheses by `HasDerivWithinAt`).
* G2 `iterate_interp_S66`: the discrete iteration `a_j ≤ C (√(a_{j-1} a_{j+1}) + a_{j-1})`
  ⇒ `a_j ≤ C' ε^(1 - j/(N+1))`.
* G3 `landau_ball_S66`: a weighted version on a ball for `iteratedFDeriv`.
-/

noncomputable section
open Set Metric
namespace GC.LongTime.Ch12

section OneD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second-order Taylor remainder bound (with the non-sharp constant `M2 * |y - x|²`). -/
theorem taylor_lite_S66 {f f' f'' : ℝ → E} {a b M2 : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivWithinAt f' (f'' x) (Icc a b) x)
    (h2 : ∀ x ∈ Icc a b, ‖f'' x‖ ≤ M2) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f y - f x - (y - x) • f' x‖ ≤ M2 * ‖y - x‖ ^ 2 := by
  have hseg : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
  have hM2 : 0 ≤ M2 := (norm_nonneg _).trans (h2 x hx)
  have hLip : ∀ t ∈ Icc a b, ‖f' t - f' x‖ ≤ M2 * ‖t - x‖ := fun t ht =>
    (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hf' h2 hx ht
  have hg : ∀ t ∈ uIcc x y,
      HasDerivWithinAt (fun t => f t - f x - (t - x) • f' x) (f' t - f' x) (uIcc x y) t := by
    intro t ht
    have h1 := (hf t (hseg ht)).mono hseg
    have h3 : HasDerivAt (fun t : ℝ => (t - x) • f' x) (f' x) t := by
      simpa using ((hasDerivAt_id t).sub_const x).smul_const (f' x)
    exact (h1.sub_const (f x)).sub h3.hasDerivWithinAt
  have hbd : ∀ t ∈ uIcc x y, ‖f' t - f' x‖ ≤ M2 * ‖y - x‖ := by
    intro t ht
    refine (hLip t (hseg ht)).trans (mul_le_mul_of_nonneg_left ?_ hM2)
    simpa [Real.norm_eq_abs] using abs_sub_left_of_mem_uIcc ht
  have := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le hg hbd
    (left_mem_uIcc) (right_mem_uIcc)
  simpa [pow_two, mul_assoc] using this

/-- pointwise two-point estimate `‖f' x‖ ≤ 2 M0 / h + M2 h` for `0 < h`, `2 h ≤ b - a`. -/
theorem landau_1d_aux_S66 {f f' f'' : ℝ → E} {a b M0 M2 : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivWithinAt f' (f'' x) (Icc a b) x)
    (h0 : ∀ x ∈ Icc a b, ‖f x‖ ≤ M0) (h2 : ∀ x ∈ Icc a b, ‖f'' x‖ ≤ M2)
    {x : ℝ} (hx : x ∈ Icc a b) {h : ℝ} (hh : 0 < h) (hab : 2 * h ≤ b - a) :
    ‖f' x‖ ≤ 2 * M0 / h + M2 * h := by
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Icc a b, |y - x| = h := by
    by_cases hc : x + h ≤ b
    · refine ⟨x + h, ⟨by linarith [hx.1], hc⟩, ?_⟩
      simp [abs_of_pos hh]
    · refine ⟨x - h, ⟨by linarith [hx.2], by linarith [hx.2]⟩, ?_⟩
      simp [abs_of_pos hh]
  have hT := taylor_lite_S66 hf hf' h2 hx hy
  rw [Real.norm_eq_abs, hyx] at hT
  have h1 : ‖(y - x) • f' x‖ = h * ‖f' x‖ := by rw [norm_smul, Real.norm_eq_abs, hyx]
  have h3 : ‖(y - x) • f' x‖ ≤ ‖f y‖ + ‖f x‖ + M2 * h ^ 2 := by
    have := norm_sub_norm_le ((y - x) • f' x) (f y - f x)
    have h4 : ‖f y - f x - (y - x) • f' x‖ = ‖(y - x) • f' x - (f y - f x)‖ := norm_sub_rev _ _
    have h5 : ‖f y - f x‖ ≤ ‖f y‖ + ‖f x‖ := norm_sub_le _ _
    linarith
  have h6 : h * ‖f' x‖ ≤ 2 * M0 + M2 * h ^ 2 := by
    have := h0 y hy; have := h0 x hx; linarith
  rw [div_add' _ _ _ hh.ne', le_div_iff₀ hh]
  nlinarith

/-- the elementary optimisation in `h`. -/
theorem landau_opt_S66 {D M0 M2 ℓ : ℝ} (hℓ : 0 < ℓ) (hM0 : 0 ≤ M0) (hM2 : 0 ≤ M2)
    (hD : ∀ h : ℝ, 0 < h → 2 * h ≤ ℓ → D ≤ 2 * M0 / h + M2 * h) :
    D ≤ 4 * (√(M0 * M2) + M0 / ℓ) := by
  have hs0 : 0 ≤ √(M0 * M2) := Real.sqrt_nonneg _
  have hq : 0 ≤ M0 / ℓ := div_nonneg hM0 hℓ.le
  rcases hM2.eq_or_lt with h2 | h2
  · have := hD (ℓ / 2) (by positivity) (by linarith)
    have e : 2 * M0 / (ℓ / 2) = 4 * (M0 / ℓ) := by field_simp; ring
    rw [← h2, e] at this
    linarith
  rcases hM0.eq_or_lt with h0 | h0
  · by_contra hcon
    have hDpos : 0 < D := by
      by_contra hn
      push Not at hn
      apply hcon
      rw [← h0] at *
      simp at *
      linarith
    set h := min (ℓ / 2) (D / (2 * M2)) with hhdef
    have hhpos : 0 < h := lt_min (by positivity) (by positivity)
    have := hD h hhpos (by linarith [min_le_left (ℓ / 2) (D / (2 * M2))])
    rw [← h0] at this
    have hle : h ≤ D / (2 * M2) := min_le_right _ _
    have : M2 * h ≤ D / 2 := by
      calc M2 * h ≤ M2 * (D / (2 * M2)) := mul_le_mul_of_nonneg_left hle hM2
        _ = D / 2 := by field_simp
    simp at *
    linarith
  · set s := √(M0 * M2) with hs
    have hspos : 0 < s := Real.sqrt_pos.2 (mul_pos h0 h2)
    have hss : s * s = M0 * M2 := Real.mul_self_sqrt (mul_pos h0 h2).le
    by_cases hc : 2 * (s / M2) ≤ ℓ
    · have := hD (s / M2) (by positivity) hc
      have e : 2 * M0 / (s / M2) = 2 * s := by
        field_simp
        nlinarith [hss]
      have e2 : M2 * (s / M2) = s := by field_simp
      rw [e, e2] at this
      linarith
    · push Not at hc
      have := hD (ℓ / 2) (by positivity) (by linarith)
      have e : 2 * M0 / (ℓ / 2) = 4 * (M0 / ℓ) := by field_simp; ring
      have e2 : M2 * (ℓ / 2) ≤ s := by
        have : ℓ / 2 ≤ s / M2 := by linarith
        calc M2 * (ℓ / 2) ≤ M2 * (s / M2) := mul_le_mul_of_nonneg_left this hM2
          _ = s := by field_simp
      rw [e] at this
      linarith

/-- **G1** Landau–Kolmogorov on an interval: `‖f'‖ ≤ 4 (√(M0 M2) + M0 / (b - a))`. -/
theorem landau_1d_S66 {f f' f'' : ℝ → E} {a b M0 M2 : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hf' : ∀ x ∈ Icc a b, HasDerivWithinAt f' (f'' x) (Icc a b) x)
    (h0 : ∀ x ∈ Icc a b, ‖f x‖ ≤ M0) (h2 : ∀ x ∈ Icc a b, ‖f'' x‖ ≤ M2) :
    ∀ x ∈ Icc a b, ‖f' x‖ ≤ 4 * (√(M0 * M2) + M0 / (b - a)) := by
  intro x hx
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  exact landau_opt_S66 (sub_pos.2 hab) ((norm_nonneg _).trans (h0 a ha))
    ((norm_nonneg _).trans (h2 a ha))
    (fun h hh hh2 => landau_1d_aux_S66 hf hf' h0 h2 hx hh hh2)

end OneD

end GC.LongTime.Ch12
