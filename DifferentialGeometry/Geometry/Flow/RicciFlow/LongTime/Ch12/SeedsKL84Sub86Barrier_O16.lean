import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86Doubling_O16

/-!
# CH12-O16 G2b-(b2) tool: shifted backward barrier for `|∂ₜR| ≤ C R²`

`backward_barrier_O16`: if `f b ≤ (β - 2Cσ₀)⁻¹` and `|f'| ≤ C f²` (left derivatives) wherever
`f > M`, with `βM < 1`, then `f t ≤ (β - 2C(σ₀ + (b - t)))⁻¹` on `[c, b]` as long as the barrier
denominator stays positive.  The barrier is shift-invariant in `σ₀`, so the estimate can be
restarted slab by slab across surgery times (KL Sublemma 86.3, step (b2)): the value reached at
the beginning of one slab is the input `σ₀` of the previous one.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace GC.LongTime.Ch12

/-- Shifted backward barrier `B(σ) = (β - 2Cσ)⁻¹` for the backward scalar-curvature estimate. -/
theorem backward_barrier_O16 {f : ℝ → ℝ} {c b M C β σ0 : ℝ} (hC : 0 < C) (hβ : 0 < β)
    (hβM : β * M < 1) (hσ0 : 0 ≤ σ0) (hden : 0 < β - 2 * C * (σ0 + (b - c)))
    (hcont : ContinuousOn f (Icc c b))
    (hdiff : ∀ t ∈ Ioc c b, DifferentiableWithinAt ℝ f (Iic t) t)
    (hP2 : ∀ t ∈ Ioc c b, M < f t → |derivWithin f (Iic t) t| ≤ C * f t ^ 2)
    (hb : f b ≤ (β - 2 * C * σ0)⁻¹) :
    ∀ t ∈ Icc c b, f t ≤ (β - 2 * C * (σ0 + (b - t)))⁻¹ := by
  intro t0 ht0
  have hbc : 0 ≤ b - c := by linarith [ht0.1, ht0.2]
  let h : ℝ → ℝ := fun σ => f (b - σ)
  let h' : ℝ → ℝ := fun σ => -derivWithin f (Iic (b - σ)) (b - σ)
  let den : ℝ → ℝ := fun σ => β - 2 * C * (σ0 + σ)
  let B : ℝ → ℝ := fun σ => (den σ)⁻¹
  let B' : ℝ → ℝ := fun σ => 2 * C / den σ ^ 2
  have hdenpos : ∀ σ, σ ≤ b - c → 0 < den σ := by
    intro σ hσ
    have : 2 * C * (σ0 + σ) ≤ 2 * C * (σ0 + (b - c)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    change 0 < β - 2 * C * (σ0 + σ)
    linarith
  have hMB : ∀ σ, 0 ≤ σ → σ ≤ b - c → M < B σ := by
    intro σ h0 h1
    have hd := hdenpos σ h1
    have hle : den σ ≤ β := by
      change β - 2 * C * (σ0 + σ) ≤ β
      have : 0 ≤ 2 * C * (σ0 + σ) := by positivity
      linarith
    have hMβ : M < β⁻¹ := by
      calc M = (β * M) * β⁻¹ := by field_simp
        _ < 1 * β⁻¹ := mul_lt_mul_of_pos_right hβM (inv_pos.mpr hβ)
        _ = β⁻¹ := one_mul _
    exact hMβ.trans_le (inv_anti₀ hd hle)
  have hh' : ∀ σ ∈ Ico (0 : ℝ) (b - c), HasDerivWithinAt h (h' σ) (Ici σ) σ := by
    intro σ hσ
    have ht : b - σ ∈ Ioc c b := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hf := (hdiff (b - σ) ht).hasDerivWithinAt
    have hlin : HasDerivWithinAt (fun σ : ℝ => b - σ) (-1) (Ici σ) σ :=
      ((hasDerivAt_id σ).const_sub b).hasDerivWithinAt
    have hmaps : MapsTo (fun σ : ℝ => b - σ) (Ici σ) (Iic (b - σ)) := by
      intro x hx; simp only [mem_Ici] at hx; simp only [mem_Iic]; linarith
    have hcomp := hf.comp σ hlin hmaps
    have heq : derivWithin f (Iic (b - σ)) (b - σ) * (-1) = h' σ := by
      simp only [h', mul_neg, mul_one]
    rw [heq] at hcomp
    exact hcomp
  have hhc : ContinuousOn h (Icc 0 (b - c)) := by
    have hmaps : MapsTo (fun σ : ℝ => b - σ) (Icc 0 (b - c)) (Icc c b) := by
      intro x hx; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    exact hcont.comp (continuousOn_const.sub continuousOn_id) hmaps
  have hBc : ContinuousOn B (Icc 0 (b - c)) := by
    refine ContinuousOn.inv₀ (continuousOn_const.sub (continuousOn_const.mul
      (continuousOn_const.add continuousOn_id))) ?_
    intro σ hσ; exact (hdenpos σ hσ.2).ne'
  have hB' : ∀ σ ∈ Ico (0 : ℝ) (b - c), HasDerivWithinAt B (B' σ) (Ici σ) σ := by
    intro σ hσ
    have hd : HasDerivAt den (-(2 * C)) σ := by
      have := (((hasDerivAt_id σ).const_add σ0).const_mul (2 * C)).const_sub β
      simpa [den, mul_one] using this
    have hinv := hd.inv (hdenpos σ hσ.2.le).ne'
    have heq : -(-(2 * C)) / den σ ^ 2 = B' σ := by simp only [neg_neg, B']
    rw [heq] at hinv
    exact hinv.hasDerivWithinAt
  have ha : h 0 ≤ B 0 := by
    change f (b - 0) ≤ (β - 2 * C * (σ0 + 0))⁻¹
    rw [sub_zero, add_zero]
    exact hb
  have bound : ∀ σ ∈ Ico (0 : ℝ) (b - c), h σ = B σ → h' σ < B' σ := by
    intro σ hσ heq
    have ht : b - σ ∈ Ioc c b := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hd := hdenpos σ hσ.2.le
    have hfM : M < f (b - σ) := by
      change f (b - σ) = B σ at heq
      rw [heq]; exact hMB σ hσ.1 hσ.2.le
    have hd2 := hP2 (b - σ) ht hfM
    have hfB : f (b - σ) = (den σ)⁻¹ := heq
    rw [hfB] at hd2
    have hneg : h' σ ≤ |derivWithin f (Iic (b - σ)) (b - σ)| := by
      simp only [h']; exact neg_le_abs _
    have hsq : C * ((den σ)⁻¹) ^ 2 < B' σ := by
      simp only [B', inv_pow, div_eq_mul_inv]
      have : 0 < (den σ ^ 2)⁻¹ := by positivity
      nlinarith
    linarith
  have hcmp := image_le_of_deriv_right_lt_deriv_boundary' hhc hh' ha hBc hB' bound
  have hσ : b - t0 ∈ Icc (0 : ℝ) (b - c) := ⟨by linarith [ht0.2], by linarith [ht0.1]⟩
  have h1 := hcmp hσ
  have : h (b - t0) = f t0 := by simp only [h, sub_sub_cancel]
  rw [this] at h1
  exact h1

end GC.LongTime.Ch12
