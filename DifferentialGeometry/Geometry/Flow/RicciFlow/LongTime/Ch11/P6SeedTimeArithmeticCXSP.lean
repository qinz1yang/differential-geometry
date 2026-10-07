import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedArithmeticCXSP

set_option autoImplicit false

/-!
# CX-SPINE G4：时间归一化到2时的真实种子尺度恒等式

时间除以 c=t/2，标量乘以 c。原半种子窗变为 [2-r²/t,2]，其归一深度恒为 H/2；
安全 κ测试半径 r/200 同时除以 √c，所以与新标量平方根的乘积仍为 √H/200。
坏种子 r≤√t/(n+1) 使新曲率趋无穷，未假设原尺度 Hr⁻² 趋无穷。
-/

namespace GC.LongTime.Ch11

open Filter
open scoped Topology

/-- 半种子窗归一化后严格落在时间1之后，深度与种子归一曲率的乘积为 H/2。 -/
theorem seed_half_window_time_normalization_CXSP {t r : ℝ}
    (hr : 0 < r) (htime : 2 * r ^ 2 < t) (H : ℝ) :
    1 < (t - r ^ 2 / 2) / (t / 2) ∧
      (t - r ^ 2 / 2) / (t / 2) < 2 ∧
      ((t / 2) * (H * (r ^ 2)⁻¹)) *
        (2 - (t - r ^ 2 / 2) / (t / 2)) = H / 2 := by
  have ht : 0 < t := by nlinarith [sq_pos_of_pos hr]
  have heq : (t - r ^ 2 / 2) / (t / 2) = 2 - r ^ 2 / t := by
    field_simp
  have hpos : 0 < r ^ 2 / t := div_pos (pow_pos hr 2) ht
  have hlt : r ^ 2 / t < 1 := (div_lt_one ht).mpr (by nlinarith [sq_nonneg r])
  rw [heq]
  refine ⟨by linarith, by linarith, ?_⟩
  field_simp
  ring

/-- r≤√t/N 在时间归一化后给新标量下界 H*N²/2。 -/
theorem seed_time_scaled_curvature_lower_CXSP {H t r N : ℝ}
    (hH : 0 < H) (ht : 0 ≤ t) (hr : 0 < r) (hN : 0 < N)
    (hsmall : r ≤ Real.sqrt t / N) :
    (H / 2) * N ^ 2 ≤ (t / 2) * (H * (r ^ 2)⁻¹) := by
  have hmul : r * N ≤ Real.sqrt t := (le_div_iff₀ hN).mp hsmall
  have hsq := pow_le_pow_left₀ (mul_pos hr hN).le hmul 2
  rw [mul_pow, Real.sq_sqrt ht] at hsq
  have heq : (t / 2) * (H * (r ^ 2)⁻¹) = ((H / 2) * t) / r ^ 2 := by ring
  rw [heq, le_div_iff₀ (pow_pos hr 2)]
  have h := mul_le_mul_of_nonneg_left hsq (half_pos hH).le
  nlinarith

/-- 同一坏种子族的新曲率与新曲率乘终端时间都趋无穷，且逐项至少1。 -/
theorem seed_time_scaled_curvature_family_CXSP {H : ℝ} (hH : 2 ≤ H)
    (t r : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (hr : ∀ n, 0 < r n)
    (hsmall : ∀ n, r n ≤ Real.sqrt (t n) / ((n : ℝ) + 1)) :
    (∀ n, 1 ≤ (t n / 2) * (H * (r n ^ 2)⁻¹)) ∧
      Tendsto (fun n => (t n / 2) * (H * (r n ^ 2)⁻¹)) atTop atTop ∧
      Tendsto (fun n => ((t n / 2) * (H * (r n ^ 2)⁻¹)) * 2) atTop atTop := by
  have hH0 : 0 < H := by linarith
  have hbound (n : ℕ) : (H / 2) * ((n : ℝ) + 1) ^ 2 ≤
      (t n / 2) * (H * (r n ^ 2)⁻¹) :=
    seed_time_scaled_curvature_lower_CXSP hH0 (ht n) (hr n) (by positivity) (hsmall n)
  have hlinear (n : ℕ) : (H / 2) * ((n : ℝ) + 1) ≤
      (t n / 2) * (H * (r n ^ 2)⁻¹) := by
    have hpow : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    exact (mul_le_mul_of_nonneg_left hpow (half_pos hH0).le).trans (hbound n)
  have hlim : Tendsto (fun n => (t n / 2) * (H * (r n ^ 2)⁻¹)) atTop atTop :=
    tendsto_atTop_mono hlinear
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).const_mul_atTop
        (half_pos hH0))
  refine ⟨?_, hlim, hlim.atTop_mul_const (by norm_num)⟩
  intro n
  have hN : 1 ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := mul_le_mul_of_nonneg_left hN (half_pos hH0).le
  nlinarith [hlinear n]

/-- κ测试半径和新曲率同时重标度，归一测试尺度保持固定正值 √H/200。 -/
theorem seed_time_normalized_kappa_scale_CXSP {H t r : ℝ}
    (hH : 0 < H) (ht : 0 < t) (hr : 0 < r) :
    (r / 200 / Real.sqrt (t / 2)) *
      Real.sqrt ((t / 2) * (H * (r ^ 2)⁻¹)) = Real.sqrt H / 200 := by
  rw [Real.sqrt_mul (half_pos ht).le, sqrt_seed_scale_CXSP hH hr]
  field_simp [(Real.sqrt_pos.mpr (half_pos ht)).ne', hr.ne']

end GC.LongTime.Ch11
