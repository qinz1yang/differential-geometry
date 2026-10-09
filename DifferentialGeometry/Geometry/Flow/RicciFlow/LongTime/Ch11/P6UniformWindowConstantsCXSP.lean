import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedWindowScaleCXSP

set_option autoImplicit false

/-!
# CX-SPINE G27：随标量上界变化但有定量深度的 window constants

只在 m=1 调用 G7 选择基础 k0/lambda0/beta0。随后 k=k0(m+1)，
lambda=lambda0/(m+1)，beta=beta0/(m+1)，保留所有预算并暴露准确 beta 衰减率。
这是数值补强，不生产 full Good、几何域或任意 M/tau 的 trace-chain 合同。
-/

open scoped NNReal

namespace GC.LongTime.Ch11

/-- 基础常数先于所有 m 选择；准确 beta0/(m+1) 支付整个 G7 数值合同。 -/
theorem exists_uniform_seed_window_constants_CXSP
    {H Δ γ : ℝ} (hH : 4 ≤ H) (Ctime Cgrad : ℝ≥0) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    ∃ k0 lam0 β0 : ℝ, 0 < k0 ∧ 0 < lam0 ∧ 0 < β0 ∧
      ∀ m : ℝ, 1 / 2 ≤ m →
      let k := k0 * (m + 1)
      let lam := lam0 / (m + 1)
      let β := β0 / (m + 1)
      0 < k ∧ 0 < lam ∧ 0 < β ∧
        2 * Real.sqrt 3 * (4 * m + max (8 * m) (2 * Real.exp 4)) ≤ k ∧
        H⁻¹ ≤ k ∧ lam ≤ Real.sqrt H / 50 ∧ 2 * lam < γ * Real.sqrt H ∧
        (Cgrad : ℝ) * lam * Real.sqrt (2 * m) ≤ 1 / 4 ∧ k * lam ^ 2 ≤ 1 ∧
        β ≤ H / 4 ∧ (Ctime : ℝ) * m * β ≤ 1 / 2 ∧
        8 * β / lam < Δ * Real.sqrt H := by
  obtain ⟨k0, lam0, β0, hk0, hlam0, hβ0, hJ0, hHi, hlamH, hlamγ, hgrad0,
    hklam, hβH, htime0, hdrift0⟩ :=
    exists_seed_window_constants_CXSP (M := 1) hH one_pos Ctime Cgrad hΔ hγ
  norm_num only [mul_one] at hJ0 hgrad0 htime0
  refine ⟨k0, lam0, β0, hk0, hlam0, hβ0, ?_⟩
  intro m hm k lam β
  have hu : 1 ≤ m + 1 := by linarith
  have hu0 : 0 < m + 1 := by linarith
  have hkle : k0 ≤ k := by dsimp only [k]; nlinarith only [hk0, hu]
  have hlam : 0 < lam := div_pos hlam0 hu0
  have hβ : 0 < β := div_pos hβ0 hu0
  have hlamle : lam ≤ lam0 := (div_le_self hlam0.le hu)
  have hβle : β ≤ β0 := (div_le_self hβ0.le hu)
  refine ⟨hk0.trans_le hkle, hlam, hβ, ?_, hHi.trans hkle, hlamle.trans hlamH,
    (mul_le_mul_of_nonneg_left hlamle (by norm_num)).trans_lt hlamγ, ?_, ?_,
    hβle.trans hβH, ?_, ?_⟩
  · let c := 2 * Real.exp 4
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    have hmax : max (8 * m) c ≤ max 8 c * (m + 1) := by
      apply max_le
      · exact (by nlinarith : 8 * m ≤ 8 * (m + 1)).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hu0.le)
      · exact (by nlinarith only [hc, hu] : c ≤ c * (m + 1)).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hu0.le)
    have hsum : 4 * m + max (8 * m) c ≤ (4 + max 8 c) * (m + 1) := by
      nlinarith only [hmax]
    have hprod := mul_le_mul_of_nonneg_left hsum
      (by positivity : 0 ≤ 2 * Real.sqrt 3)
    have hbase := mul_le_mul_of_nonneg_right hJ0 hu0.le
    dsimp only [k]
    dsimp only [c] at hprod
    nlinarith only [hprod, hbase]
  · have hsqrt : Real.sqrt (2 * m) ≤ Real.sqrt 2 * (m + 1) := by
      calc
        Real.sqrt (2 * m) ≤ Real.sqrt (2 * (m + 1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg m])
        _ = Real.sqrt 2 * (m + 1) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hu0.le]
    calc
      (Cgrad : ℝ) * lam * Real.sqrt (2 * m) ≤
          (Cgrad : ℝ) * lam * (Real.sqrt 2 * (m + 1)) :=
        mul_le_mul_of_nonneg_left hsqrt (mul_nonneg Cgrad.coe_nonneg hlam.le)
      _ = (Cgrad : ℝ) * lam0 * Real.sqrt 2 := by dsimp only [lam]; field_simp
      _ ≤ 1 / 4 := hgrad0
  · calc
      k * lam ^ 2 = k0 * lam0 ^ 2 / (m + 1) := by
        dsimp only [k, lam]
        field_simp
      _ ≤ k0 * lam0 ^ 2 := div_le_self (mul_nonneg hk0.le (sq_nonneg _)) hu
      _ ≤ 1 := hklam
  · have hratio : m / (m + 1) ≤ 1 := (div_le_one hu0).mpr (by linarith)
    calc
      (Ctime : ℝ) * m * β = ((Ctime : ℝ) * β0) * (m / (m + 1)) := by
        dsimp only [β]
        ring
      _ ≤ ((Ctime : ℝ) * β0) * 1 :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg Ctime.coe_nonneg hβ0.le)
      _ ≤ 1 / 2 := by simpa only [mul_one] using htime0
  · have heq : 8 * β / lam = 8 * β0 / lam0 := by
      dsimp only [β, lam]
      field_simp
    rw [heq]
    exact hdrift0

/-- 同一基础常数的 physical-scale 版本；beta 衰减率仍明确且先于 queries。 -/
theorem exists_uniform_seed_window_scale_CXSP
    {H Δ γ : ℝ} (hH : 4 ≤ H) (Ctime Cgrad : ℝ≥0) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    ∃ k0 lam0 β0 : ℝ, 0 < k0 ∧ 0 < lam0 ∧ 0 < β0 ∧
      ∀ m : ℝ, 1 / 2 ≤ m → ∀ r t : ℝ, 0 < r → 2 * r ^ 2 < t →
      let Q := H * (r ^ 2)⁻¹
      let ell := (lam0 / (m + 1)) / Real.sqrt Q
      let K := (k0 * (m + 1)) * Q
      let tau := (β0 / (m + 1)) / Q
      let a := t - tau
      0 < ell ∧ 0 < tau ∧ tau ≤ r ^ 2 / 4 ∧ 1 ≤ Q * a ∧
        ell ≤ r / 50 ∧ 2 * ell < γ * r ∧
        (Cgrad : ℝ) * ell * Real.sqrt (2 * (m * Q)) ≤ 1 / 4 ∧
        K * ell ^ 2 ≤ 1 ∧ (r ^ 2)⁻¹ ≤ K ∧
        (2 * Real.sqrt 3 * (4 * m + max (8 * m) (2 * Real.exp 4))) * Q ≤ K ∧
        (Ctime : ℝ) * (m * Q) * tau ≤ 1 / 2 ∧ 8 * tau / ell < Δ * r := by
  obtain ⟨k0, lam0, β0, hk0, hlam0, hβ0, hconst⟩ :=
    exists_uniform_seed_window_constants_CXSP hH Ctime Cgrad hΔ hγ
  refine ⟨k0, lam0, β0, hk0, hlam0, hβ0, ?_⟩
  intro m hm r t hr ht
  obtain ⟨_hk, hlam, hβ, hJ, hHi, hlamH, hlamγ, hgrad, hklam, hβH, htime, hdrift⟩ :=
    hconst m hm
  exact seed_window_scale_of_constants_CXSP hH (by linarith) Ctime Cgrad hlam hβ hJ hHi
    hlamH hlamγ hgrad hklam hβH htime hdrift r t hr ht

end GC.LongTime.Ch11
