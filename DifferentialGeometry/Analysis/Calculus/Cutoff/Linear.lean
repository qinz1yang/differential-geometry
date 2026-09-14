import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ballCutoff_comp_linear_derivative_bounds (L : E →L[ℝ] ℝ)
    (center r R : ℝ) (hr : 0 ≤ r) (hrR : r < R) (x : E) :
    ‖fderiv ℝ (fun y => ballCutoff center r R (L y)) x‖ ≤ ballCutoffFDerivBound r R * ‖L‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => ballCutoff center r R (L y))) x‖ ≤
        ballCutoffFDeriv2Bound r R * ‖L‖ ^ 2 := by
  have hd (y : E) : fderiv ℝ (fun z => ballCutoff center r R (L z)) y =
      (ballCutoffFDeriv center r R (L y)).comp L :=
    ((hasFDerivAt_ballCutoff center r R (L y)).comp y L.hasFDerivAt).fderiv
  constructor
  · rw [hd x]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_ballCutoffFDeriv_le hr hrR (L x)) (norm_nonneg L))
  · have hdf := ((hasFDerivAt_ballCutoffFDeriv center r R (L x)).comp x L.hasFDerivAt).clm_comp
      (hasFDerivAt_const (c := L) (x := x))
    have he : fderiv ℝ (fderiv ℝ (fun y => ballCutoff center r R (L y))) x =
        ((ContinuousLinearMap.compL ℝ E ℝ ℝ).flip L).comp
          ((ballCutoffFDeriv2 center r R (L x)).comp L) := by
      rw [funext hd]
      simpa only [ContinuousLinearMap.comp_zero, zero_add, Function.comp_def] using hdf.fderiv
    have hpre : ‖(ContinuousLinearMap.compL ℝ E ℝ ℝ).flip L‖ ≤ ‖L‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
      intro P
      exact (ContinuousLinearMap.opNorm_comp_le P L).trans_eq (mul_comm _ _)
    rw [he]
    calc
      ‖((ContinuousLinearMap.compL ℝ E ℝ ℝ).flip L).comp
          ((ballCutoffFDeriv2 center r R (L x)).comp L)‖ ≤
          ‖L‖ * (ballCutoffFDeriv2Bound r R * ‖L‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hpre ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_ballCutoffFDeriv2_le hr hrR (L x)) (norm_nonneg L)))
            (norm_nonneg _) (norm_nonneg L))
      _ = ballCutoffFDeriv2Bound r R * ‖L‖ ^ 2 := by ring


theorem ballCutoff_comp_linear_half_radius_derivative_bounds (L : E →L[ℝ] ℝ)
    (hL : ‖L‖ ≤ 1) (center d : ℝ) (hd : 0 < d) (x : E) :
    ‖fderiv ℝ (fun y => ballCutoff center (d / 2) d (L y)) x‖ ≤
        4 * CutoffProfile.derivBound / d ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => ballCutoff center (d / 2) d (L y))) x‖ ≤
        16 * CutoffProfile.derivBound / d ^ 2 := by
  have hr : 0 ≤ d / 2 := by positivity
  have hrR : d / 2 < d := by linarith
  have h := ballCutoff_comp_linear_derivative_bounds L center (d / 2) d hr hrR x
  have he₁ : ballCutoffFDerivBound (d / 2) d = (8 / 3 : ℝ) * CutoffProfile.derivBound / d := by
    dsimp only [ballCutoffFDerivBound]
    field_simp
    ring
  have he₂ : ballCutoffFDeriv2Bound (d / 2) d = (88 / 9 : ℝ) * CutoffProfile.derivBound / d ^ 2 := by
    dsimp only [ballCutoffFDeriv2Bound]
    field_simp
    ring
  have hb₁ := mul_le_mul_of_nonneg_left hL (ballCutoffFDerivBound_nonneg hr hrR)
  have hb₂ := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg L) zero_le_one).mpr hL) (ballCutoffFDeriv2Bound_nonneg hr hrR)
  rw [mul_one, he₁] at hb₁
  rw [one_pow, mul_one, he₂] at hb₂
  rw [he₁, he₂] at h
  constructor
  · refine (h.1.trans hb₁).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [CutoffProfile.derivBound_nonneg]) hd.le
  · refine (h.2.trans hb₂).trans ?_
    exact div_le_div_of_nonneg_right (by nlinarith [CutoffProfile.derivBound_nonneg]) (sq_nonneg d)

end DifferentialGeometry.Analysis
