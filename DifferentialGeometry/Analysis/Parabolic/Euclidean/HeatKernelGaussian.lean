import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLp

noncomputable section

open Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem baseHeat_le (x : V) :
    baseHeat x ≤ (baseHeatMass V)⁻¹ := by
  unfold baseHeat
  have hexp : Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg ‖x‖))
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hexp
      (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)

theorem baseHeat_decay {R : ℝ} (hR : 0 ≤ R) {x : V} (hx : R ≤ ‖x‖) :
    baseHeat x ≤
      (baseHeatMass V)⁻¹ * Real.exp (-(4 : ℝ)⁻¹ * R ^ 2) := by
  have hsq : R ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ hR (norm_nonneg x)).2 hx
  have harg : -(4 : ℝ)⁻¹ * ‖x‖ ^ 2 ≤ -(4 : ℝ)⁻¹ * R ^ 2 := by
    nlinarith
  unfold baseHeat
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
    (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)

theorem baseD1Maj_decay {R Q : ℝ} (hR : 0 ≤ R) {x : V}
    (hlo : R ≤ ‖x‖) (hhi : ‖x‖ ≤ Q) :
    baseD1Maj x ≤
      ((2 : ℝ)⁻¹ * Q) *
        ((baseHeatMass V)⁻¹ *
          Real.exp (-(4 : ℝ)⁻¹ * R ^ 2)) := by
  unfold baseD1Maj
  have hQ0 : 0 ≤ Q := (norm_nonneg x).trans hhi
  have hheat := baseHeat_decay hR hlo
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hhi (by positivity)) hheat
    (baseHeat_nonneg x) (mul_nonneg (by positivity) hQ0)

theorem baseD2Maj_decay {R Q : ℝ} (hR : 0 ≤ R) {x : V}
    (hlo : R ≤ ‖x‖) (hhi : ‖x‖ ≤ Q) :
    baseD2Maj x ≤
      ((4 : ℝ)⁻¹ * Q ^ 2 + (2 : ℝ)⁻¹) *
        ((baseHeatMass V)⁻¹ *
          Real.exp (-(4 : ℝ)⁻¹ * R ^ 2)) := by
  unfold baseD2Maj
  have hQ0 : 0 ≤ Q := (norm_nonneg x).trans hhi
  have hsq : ‖x‖ ^ 2 ≤ Q ^ 2 :=
    (sq_le_sq₀ (norm_nonneg x) hQ0).2 hhi
  have hcoeff :
      (4 : ℝ)⁻¹ * ‖x‖ ^ 2 + (2 : ℝ)⁻¹ ≤
        (4 : ℝ)⁻¹ * Q ^ 2 + (2 : ℝ)⁻¹ := by
    gcongr
  have hheat := baseHeat_decay hR hlo
  exact mul_le_mul hcoeff hheat (baseHeat_nonneg x)
    (add_nonneg (mul_nonneg (by positivity) (sq_nonneg Q)) (by positivity))

theorem heatKernel_le (t : ℝ) (x : V) :
    heatKernel t x ≤
      ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (baseHeatMass V)⁻¹ := by
  unfold heatKernel
  exact mul_le_mul_of_nonneg_left (baseHeat_le _)
    (inv_nonneg.mpr (pow_nonneg (by simp [heatScale]) _))

theorem heatKernel_half {t s : ℝ} (ht : 0 < t) (_hs : 0 ≤ s)
    (hst : s ≤ t / 2) (x : V) :
    heatKernel (t - s) x ≤
      ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
        (baseHeatMass V)⁻¹ := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hdiff : 0 < t - s := by linarith
  have htime : t / 2 ≤ t - s := by linarith
  have hscale : heatScale (t / 2) ≤ heatScale (t - s) := by
    exact Real.sqrt_le_sqrt htime
  have hpow :
      (heatScale (t / 2)) ^ Module.finrank ℝ V ≤
        (heatScale (t - s)) ^ Module.finrank ℝ V :=
    pow_le_pow_left₀ (heatScale_pos hhalf).le hscale _
  have hinv :
      ((heatScale (t - s)) ^ Module.finrank ℝ V)⁻¹ ≤
        ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ := by
    exact (inv_le_inv₀
      (pow_pos (heatScale_pos hdiff) _)
      (pow_pos (heatScale_pos hhalf) _)).2 hpow
  exact (heatKernel_le (t - s) x).trans
    (mul_le_mul_of_nonneg_right hinv
      (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le))

theorem heatKernel_decay {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    {x : V} (hx : R * heatScale t ≤ ‖x‖) :
    heatKernel t x ≤
      ((heatScale t) ^ Module.finrank ℝ V)⁻¹ *
        ((baseHeatMass V)⁻¹ * Real.exp (-(4 : ℝ)⁻¹ * R ^ 2)) := by
  have hs : 0 < heatScale t := heatScale_pos ht
  have hscaled : R ≤ ‖(heatScale t)⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
    have hdiv : R ≤ ‖x‖ / heatScale t := (le_div_iff₀ hs).2 hx
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  unfold heatKernel
  exact mul_le_mul_of_nonneg_left (baseHeat_decay hR hscaled)
    (inv_nonneg.mpr (pow_nonneg hs.le _))

theorem heatKernel_early {t s R : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hst : s ≤ t / 2) (hR : 0 ≤ R) {x : V}
    (hx : R * heatScale t ≤ ‖x‖) :
    heatKernel (t - s) x ≤
      ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
        ((baseHeatMass V)⁻¹ *
          Real.exp (-(4 : ℝ)⁻¹ * R ^ 2)) := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hdiff : 0 < t - s := by linarith
  have htime_lo : t / 2 ≤ t - s := by linarith
  have htime_hi : t - s ≤ t := by linarith
  have hscale_lo : heatScale (t / 2) ≤ heatScale (t - s) :=
    Real.sqrt_le_sqrt htime_lo
  have hscale_hi : heatScale (t - s) ≤ heatScale t :=
    Real.sqrt_le_sqrt htime_hi
  have hx' : R * heatScale (t - s) ≤ ‖x‖ :=
    (mul_le_mul_of_nonneg_left hscale_hi hR).trans hx
  have hpow :
      (heatScale (t / 2)) ^ Module.finrank ℝ V ≤
        (heatScale (t - s)) ^ Module.finrank ℝ V :=
    pow_le_pow_left₀ (heatScale_pos hhalf).le hscale_lo _
  have hinv :
      ((heatScale (t - s)) ^ Module.finrank ℝ V)⁻¹ ≤
        ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ := by
    exact (inv_le_inv₀
      (pow_pos (heatScale_pos hdiff) _)
      (pow_pos (heatScale_pos hhalf) _)).2 hpow
  exact (heatKernel_decay hdiff hR hx').trans
    (mul_le_mul_of_nonneg_right hinv
      (mul_nonneg
        (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
        (Real.exp_pos _).le))

omit [FiniteDimensional ℝ V] in
theorem earlyScaled_lo {t s R : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hst : s ≤ t / 2) (_hR : 0 ≤ R) {x : V}
    (hx : R * heatScale t ≤ ‖x‖) :
    R ≤ ‖(heatScale (t - s))⁻¹ • x‖ := by
  have hdiff : 0 < t - s := by linarith
  have htime : t - s ≤ t := by linarith
  have hscale : heatScale (t - s) ≤ heatScale t :=
    Real.sqrt_le_sqrt htime
  have hinv : (heatScale t)⁻¹ ≤ (heatScale (t - s))⁻¹ :=
    (inv_le_inv₀ (heatScale_pos ht) (heatScale_pos hdiff)).2 hscale
  have hdiv : R ≤ (heatScale t)⁻¹ * ‖x‖ := by
    have := (le_div_iff₀ (heatScale_pos ht)).2 hx
    simpa only [div_eq_mul_inv, mul_comm] using this
  rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (heatScale_pos hdiff)]
  exact hdiv.trans
    (mul_le_mul_of_nonneg_right hinv (norm_nonneg x))

omit [FiniteDimensional ℝ V] in
theorem earlyScaled_hi {t s Q : ℝ} (ht : 0 < t) (_hs : 0 ≤ s)
    (hst : s ≤ t / 2) (_hQ : 0 ≤ Q) {x : V}
    (hx : ‖x‖ ≤ Q * heatScale t) :
    ‖(heatScale (t - s))⁻¹ • x‖ ≤ Real.sqrt 2 * Q := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hdiff : 0 < t - s := by linarith
  have htime : t / 2 ≤ t - s := by linarith
  have hscale : heatScale (t / 2) ≤ heatScale (t - s) :=
    Real.sqrt_le_sqrt htime
  have hinv : (heatScale (t - s))⁻¹ ≤ (heatScale (t / 2))⁻¹ :=
    (inv_le_inv₀ (heatScale_pos hdiff) (heatScale_pos hhalf)).2 hscale
  have hscaleEq :
      heatScale t = Real.sqrt 2 * heatScale (t / 2) := by
    unfold heatScale
    calc
      Real.sqrt t = Real.sqrt (2 * (t / 2)) := by congr 1; ring
      _ = Real.sqrt 2 * Real.sqrt (t / 2) :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (t / 2)
  rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (heatScale_pos hdiff)]
  calc
    (heatScale (t - s))⁻¹ * ‖x‖ ≤
        (heatScale (t / 2))⁻¹ * ‖x‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg x)
    _ ≤ (heatScale (t / 2))⁻¹ * (Q * heatScale t) :=
      mul_le_mul_of_nonneg_left hx
        (inv_nonneg.mpr (heatScale_pos hhalf).le)
    _ = Real.sqrt 2 * Q := by
      rw [hscaleEq]
      field_simp [(heatScale_pos hhalf).ne']

theorem heatD1Maj_early {t s R Q : ℝ} (ht : 0 < t) (_hs : 0 ≤ s)
    (hst : s ≤ t / 2) (hR : 0 ≤ R) {x : V}
    (hlo : R ≤ ‖(heatScale (t - s))⁻¹ • x‖)
    (hhi : ‖(heatScale (t - s))⁻¹ • x‖ ≤ Q) :
    heatD1Maj (t - s) x ≤
      ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale (t / 2))⁻¹ *
          (((2 : ℝ)⁻¹ * Q) *
            ((baseHeatMass V)⁻¹ *
              Real.exp (-(4 : ℝ)⁻¹ * R ^ 2))) := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hdiff : 0 < t - s := by linarith
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hhi
  have htime : t / 2 ≤ t - s := by linarith
  have hscale : heatScale (t / 2) ≤ heatScale (t - s) :=
    Real.sqrt_le_sqrt htime
  have hinv : (heatScale (t - s))⁻¹ ≤ (heatScale (t / 2))⁻¹ :=
    (inv_le_inv₀ (heatScale_pos hdiff) (heatScale_pos hhalf)).2 hscale
  have hpow :
      (heatScale (t / 2)) ^ Module.finrank ℝ V ≤
        (heatScale (t - s)) ^ Module.finrank ℝ V :=
    pow_le_pow_left₀ (heatScale_pos hhalf).le hscale _
  have hinvPow :
      ((heatScale (t - s)) ^ Module.finrank ℝ V)⁻¹ ≤
        ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ := by
    exact (inv_le_inv₀
      (pow_pos (heatScale_pos hdiff) _)
      (pow_pos (heatScale_pos hhalf) _)).2 hpow
  unfold heatD1Maj
  have hfront : 0 ≤
      ((heatScale (t - s)) ^ Module.finrank ℝ V)⁻¹ *
        (heatScale (t - s))⁻¹ :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos hdiff).le _))
      (inv_nonneg.mpr (heatScale_pos hdiff).le)
  have htail : 0 ≤
      (((2 : ℝ)⁻¹ * Q) *
        ((baseHeatMass V)⁻¹ * Real.exp (-(4 : ℝ)⁻¹ * R ^ 2))) :=
    mul_nonneg (mul_nonneg (by positivity) hQ0)
      (mul_nonneg (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
        (Real.exp_pos _).le)
  have hfront_le :
      ((heatScale (t - s)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t - s))⁻¹ ≤
        ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t / 2))⁻¹ := by
    exact mul_le_mul hinvPow hinv
      (inv_nonneg.mpr (heatScale_pos hdiff).le)
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos hhalf).le _))
  calc
    ((heatScale (t - s)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t - s))⁻¹ *
            baseD1Maj ((heatScale (t - s))⁻¹ • x) ≤
        ((heatScale (t - s)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t - s))⁻¹ *
            (((2 : ℝ)⁻¹ * Q) *
              ((baseHeatMass V)⁻¹ *
                Real.exp (-(4 : ℝ)⁻¹ * R ^ 2))) := by
      exact mul_le_mul_of_nonneg_left (baseD1Maj_decay hR hlo hhi) hfront
    _ ≤ ((heatScale (t / 2)) ^ Module.finrank ℝ V)⁻¹ *
          (heatScale (t / 2))⁻¹ *
            (((2 : ℝ)⁻¹ * Q) *
              ((baseHeatMass V)⁻¹ *
                Real.exp (-(4 : ℝ)⁻¹ * R ^ 2))) := by
      exact mul_le_mul_of_nonneg_right hfront_le htail

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
