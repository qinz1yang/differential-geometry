import Mathlib

/-!
# CH12-S87: the numeric identities of the per-`w` step of `hsub86N_S87`

With `r := κ₀ r0 / 2`, `Mb := 16 A' / r0²`, `Q = 32 C2 A'`, `κ₀ = 1/(10(Q+1))`, `K = C Q κ₀²/4`,
`τ₂ = τs κ₀²/4`: radius (`20 r ≤ (√(2 C2 Mb))⁻¹`), Rm bound (`C · 2 C2 Mb = K / r²`), depth
(`τs r² = τ₂ r0²`), `1 ≤ Mb`, and the output shape `K / r² = (C Q) (r0²)⁻¹`.
-/

set_option autoImplicit false

namespace GC.LongTime.Ch12

theorem arith_ball_S87 {Q C2 A' κ₀ r0 : ℝ} (hQdef : Q = 32 * C2 * A')
    (hκdef : κ₀ = 1 / (10 * (Q + 1))) (hQ : 0 < Q) (hr0 : 0 < r0) :
    20 * (κ₀ * r0 / 2) ≤ (Real.sqrt (2 * C2 * (16 * A' / r0 ^ 2)))⁻¹ := by
  have hL : 2 * C2 * (16 * A' / r0 ^ 2) = Q / r0 ^ 2 := by rw [hQdef]; ring
  have hs : Real.sqrt (Q / r0 ^ 2) ≤ (Q + 1) / r0 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hpos : 0 < Real.sqrt (Q / r0 ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [hL]
  have h20 : 20 * (κ₀ * r0 / 2) = ((Q + 1) / r0)⁻¹ := by rw [hκdef]; field_simp; ring
  rw [h20]
  exact inv_anti₀ hpos hs

theorem arith_rm_S87 {Q C C2 A' κ₀ K r0 : ℝ} (hQdef : Q = 32 * C2 * A') (hKdef : K = C * Q * κ₀ ^ 2 / 4)
    (hκ : 0 < κ₀) (hr0 : 0 < r0) :
    C * (2 * C2 * (16 * A' / r0 ^ 2)) = K / (κ₀ * r0 / 2) ^ 2 := by
  rw [hKdef, hQdef]; field_simp; ring

theorem arith_out_S87 {Q C κ₀ K r0 : ℝ} (hKdef : K = C * Q * κ₀ ^ 2 / 4)
    (hκ : 0 < κ₀) (hr0 : 0 < r0) :
    K / (κ₀ * r0 / 2) ^ 2 = (C * Q) * (r0 ^ 2)⁻¹ := by
  rw [hKdef]; field_simp; ring

theorem arith_depth_S87 {τs τ₂ κ₀ r0 : ℝ} (hτ₂def : τ₂ = τs * κ₀ ^ 2 / 4) :
    τs * (κ₀ * r0 / 2) ^ 2 = τ₂ * r0 ^ 2 := by
  rw [hτ₂def]; ring

theorem arith_Mb_S87 {A' r0 : ℝ} (hr0 : 0 < r0) (hr0A : r0 ^ 2 ≤ A') : 1 ≤ 16 * A' / r0 ^ 2 := by
  rw [le_div_iff₀ (by positivity)]; nlinarith

end GC.LongTime.Ch12
