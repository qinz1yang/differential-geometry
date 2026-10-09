import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedWindowScaleCXSP
import Mathlib.Basic.ENNReal.Real

set_option autoImplicit false

/-!
# CX-SPINE G26：固定 seed survival 的阈值与距离余量

G7 已生产无量纲 k、lambda、beta；此处补固定 m≥1/2 的准确阈值和 HI 商式。
终端距离≤d0*r 与正余量 Delta/gamma 支付 strict margin，不从开球成员关系默取统一余量。
-/

open scoped ENNReal NNReal

namespace GC.LongTime.Ch11

/-- 固定 m 和 H0 给准确 L=mH0、canonical threshold 及 G25 所用 HI 商式。 -/
theorem seed_survival_thresholds_CXSP
    {H0 Kwin m r : ℝ} (hH : 4 ≤ H0) (hKw : 2 * Kwin ≤ H0)
    (hm : 1 / 2 ≤ m) (hr : 0 < r) :
    let Q := H0 * (r ^ 2)⁻¹
    0 < Q ∧ (m * Q) * r ^ 2 = m * H0 ∧
      Kwin * (r ^ 2)⁻¹ ≤ Q / 2 ∧ Q / 2 ≤ m * Q ∧
      2 * Real.sqrt 3 * (4 * (m * Q) / Q +
        max (8 * (m * Q) / Q) (2 * Real.exp 4)) * Q =
        (2 * Real.sqrt 3 * (4 * m + max (8 * m) (2 * Real.exp 4))) * Q := by
  intro Q
  have hH0 : 0 < H0 := by linarith
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have hQ : 0 < Q := mul_pos hH0 hi
  refine ⟨hQ, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q]
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ (sq_pos_of_pos hr).ne', mul_one]
  · have hhalf : Kwin ≤ H0 / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hhalf hi.le
    dsimp only [Q]
    nlinarith only [hmul]
  · have hmul := mul_le_mul_of_nonneg_right hm hQ.le
    linarith only [hmul]
  · have h4 : 4 * (m * Q) / Q = 4 * m := by
      rw [← mul_assoc, mul_div_cancel_right₀ _ hQ.ne']
    have h8 : 8 * (m * Q) / Q = 8 * m := by
      rw [← mul_assoc, mul_div_cancel_right₀ _ hQ.ne']
    rw [h4, h8]

/-- 显式正距离余量支付同一 Afac 空间域与 ENNReal strict first-exit margin。 -/
theorem seed_survival_margin_CXSP
    {Afac d0 Δ γ r ell tau : ℝ} {d : ℝ≥0∞}
    (hd0 : 0 ≤ d0) (hΔ : 0 < Δ) (hr : 0 < r) (hell : 0 < ell) (htau : 0 ≤ tau)
    (hbuffer : d0 + Δ + γ ≤ Afac) (hellγ : 2 * ell < γ * r)
    (hdrift : 8 * tau / ell < Δ * r) (hd : d ≤ ENNReal.ofReal (d0 * r)) :
    (d0 + Δ) * r + 2 * ell ≤ Afac * r ∧
      d + ENNReal.ofReal ((8 / ell) * tau) < ENNReal.ofReal ((d0 + Δ) * r) := by
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hbuffer hr.le
    nlinarith only [hmul, hellγ]
  · have hnonneg : 0 ≤ (8 / ell) * tau :=
      mul_nonneg (div_nonneg (by norm_num) hell.le) htau
    calc
      d + ENNReal.ofReal ((8 / ell) * tau) ≤
          ENNReal.ofReal (d0 * r) + ENNReal.ofReal ((8 / ell) * tau) :=
        add_le_add hd le_rfl
      _ = ENNReal.ofReal (d0 * r + (8 / ell) * tau) :=
        (ENNReal.ofReal_add (mul_nonneg hd0 hr.le) hnonneg).symm
      _ < ENNReal.ofReal ((d0 + Δ) * r) := by
        apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by linarith) hr)).mpr
        have hdrift' : (8 / ell) * tau < Δ * r := by
          convert hdrift using 1
          ring
        nlinarith only [hdrift']

end GC.LongTime.Ch11
