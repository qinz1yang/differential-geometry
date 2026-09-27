import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.HarmonicMeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem harmonic_integral_norm_sq_le_radius_ratio_sq
    {f : ℂ → F} {c : ℂ} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 2)
    (hf : HarmonicOnNhd f (Metric.ball c R))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball c R)) :
    (∫ z in Metric.ball c r, ‖f z‖ ^ 2) ≤
      16 * (r / R) ^ 2 * ∫ z in Metric.ball c R, ‖f z‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpt (x : ℂ) (hx : x ∈ Metric.ball c r) :
      ‖f x‖ ^ 2 ≤ (16 / (Real.pi * R ^ 2)) * ∫ z in Metric.ball c R, ‖f z‖ ^ 2 := by
    have hxR : dist x c < R / 2 := (Metric.mem_ball.mp hx).trans_le hrR
    have hsub : Metric.closedBall x (R / 2) ⊆ Metric.ball c R := by
      intro y hy
      exact Metric.mem_ball.mpr (by linarith [Metric.mem_closedBall.mp hy, dist_triangle y x c])
    have hm := harmonic_norm_sq_le_integral_norm_sq (half_pos hR) (hf.mono hsub)
    have hmono : (∫ y in Metric.closedBall x (R / 2), ‖f y‖ ^ 2) ≤
        ∫ y in Metric.ball c R, ‖f y‖ ^ 2 :=
      setIntegral_mono_set hi (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall hsub)
    have hc : 0 ≤ 4 / (Real.pi * (R / 2) ^ 2) := by positivity
    have ht := hm.trans (mul_le_mul_of_nonneg_left hmono hc)
    have hratio : 4 / (Real.pi * (R / 2) ^ 2) = 16 / (Real.pi * R ^ 2) := by ring
    rwa [hratio] at ht
  have hsub : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball (by linarith)
  have hh : (∫ z in Metric.ball c r, ‖f z‖ ^ 2) ≤
      ∫ _z in Metric.ball c r,
        (16 / (Real.pi * R ^ 2)) * ∫ z in Metric.ball c R, ‖f z‖ ^ 2 := by
    apply integral_mono_ae (hi.mono_set hsub) (integrable_const _)
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hpt x hx
  have hvol : volume.real (Metric.ball c r) = Real.pi * r ^ 2 := by
    rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr, ENNReal.coe_toReal]
    change r ^ 2 * Real.pi = Real.pi * r ^ 2
    ring
  rw [integral_const, Measure.real, Measure.restrict_apply_univ,
    ← Measure.real, smul_eq_mul, hvol] at hh
  have heq : (Real.pi * r ^ 2) * ((16 / (Real.pi * R ^ 2)) *
      ∫ z in Metric.ball c R, ‖f z‖ ^ 2) =
      16 * (r / R) ^ 2 * ∫ z in Metric.ball c R, ‖f z‖ ^ 2 := by
    field_simp [Real.pi_ne_zero, hR.ne']
  exact hh.trans_eq heq

theorem harmonic_integral_derivative_sq_le_radius_ratio_sq
    {f : ℂ → ℝ} {c : ℂ} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 2)
    (hf : HarmonicOnNhd f (Metric.ball c R))
    (hi : IntegrableOn (fun z => (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2)
      (Metric.ball c R)) :
    (∫ z in Metric.ball c r, (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2) ≤
      16 * (r / R) ^ 2 * ∫ z in Metric.ball c R,
        (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 := by
  let g : ℂ → ℂ := fun z => fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I
  have hg : HarmonicOnNhd g (Metric.ball c R) :=
    fun z hz => (HarmonicAt.analyticAt_complex_partial (hf z hz)).harmonicAt
  have heq (z : ℂ) : ‖g z‖ ^ 2 = (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2 := by
    rw [Complex.sq_norm]
    simp [g, Complex.normSq_apply]
    ring
  have hgi : IntegrableOn (fun z => ‖g z‖ ^ 2) (Metric.ball c R) := by simpa only [heq] using hi
  simpa only [heq] using harmonic_integral_norm_sq_le_radius_ratio_sq hR hr hrR hg hgi

end DifferentialGeometry.Analysis

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem holomorphic_norm_deriv_sq_le_integral_norm_sq
    {f : ℂ → ℂ} {c x : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball c R))
    (hx : x ∈ Metric.ball c (R / 4)) :
    ‖deriv f x‖ ^ 2 ≤ (256 / (Real.pi * R ^ 4)) * ∫ z in Metric.ball c R, ‖f z‖ ^ 2 := by
  let E := ∫ z in Metric.ball c R, ‖f z‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg fun z => sq_nonneg _
  let C := Real.sqrt ((16 / (Real.pi * R ^ 2)) * E)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCeq : C ^ 2 = (16 / (Real.pi * R ^ 2)) * E := Real.sq_sqrt (by positivity)
  have hball : Metric.closedBall x (R / 4) ⊆ Metric.ball c (R / 2) := by
    intro y hy
    exact Metric.mem_ball.mpr (by
      linarith [Metric.mem_closedBall.mp hy, Metric.mem_ball.mp hx, dist_triangle y x c])
  have hballR : Metric.closedBall x (R / 4) ⊆ Metric.ball c R :=
    hball.trans (Metric.ball_subset_ball (by linarith))
  have hnorm (y : ℂ) (hy : y ∈ Metric.closedBall x (R / 4)) : ‖f y‖ ≤ C := by
    have hyR := hball hy
    have hsub : Metric.closedBall y (R / 2) ⊆ Metric.ball c R := by
      intro z hz
      exact Metric.mem_ball.mpr (by
        linarith [Metric.mem_closedBall.mp hz, Metric.mem_ball.mp hyR, dist_triangle z y c])
    have hm := harmonic_norm_sq_le_integral_norm_sq (half_pos hR)
      (fun z hz => (hf z (hsub hz)).harmonicAt)
    have hmono : (∫ z in Metric.closedBall y (R / 2), ‖f z‖ ^ 2) ≤ E :=
      setIntegral_mono_set hi (Eventually.of_forall fun z => sq_nonneg _)
        (Eventually.of_forall hsub)
    have hratio : 4 / (Real.pi * (R / 2) ^ 2) = 16 / (Real.pi * R ^ 2) := by ring
    rw [hratio] at hm
    have hh := hm.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
    exact (sq_le_sq₀ (norm_nonneg _) hC).mp (hh.trans_eq hCeq.symm)
  have hdc : DiffContOnCl ℂ f (Metric.ball x (R / 4)) :=
    ⟨(hf.mono (Metric.ball_subset_closedBall.trans hballR)).differentiableOn,
      (hf.continuousOn.mono hballR).mono Metric.closure_ball_subset_closedBall⟩
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < R / 4)
    hdc (fun y hy => hnorm y (Metric.sphere_subset_closedBall hy))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [div_pow, hCeq] at hsq
  have heq : ((16 / (Real.pi * R ^ 2)) * E) / (R / 4) ^ 2 =
      (256 / (Real.pi * R ^ 4)) * E := by ring
  exact hsq.trans_eq heq

end DifferentialGeometry.Analysis

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem holomorphic_integral_sub_center_sq_le_radius_ratio_pow_four
    {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 4)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball c R)) :
    (∫ z in Metric.ball c r, ‖f z - f c‖ ^ 2) ≤
      256 * (r / R) ^ 4 * ∫ z in Metric.ball c R, ‖f z‖ ^ 2 := by
  let E := ∫ z in Metric.ball c R, ‖f z‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg fun z => sq_nonneg _
  let C := Real.sqrt ((256 / (Real.pi * R ^ 4)) * E)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCeq : C ^ 2 = (256 / (Real.pi * R ^ 4)) * E := Real.sq_sqrt (by positivity)
  have hder (x : ℂ) (hx : x ∈ Metric.ball c (R / 4)) : ‖deriv f x‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg _) hC).mp
    exact (holomorphic_norm_deriv_sq_le_integral_norm_sq hR hf hi hx).trans_eq hCeq.symm
  have hbd : Metric.closedBall c r ⊆ Metric.ball c R := Metric.closedBall_subset_ball (by linarith)
  have hfi : IntegrableOn (fun z => ‖f z - f c‖ ^ 2) (Metric.ball c r) := by
    exact (((hf.continuousOn.mono hbd).sub continuousOn_const).norm.pow 2).integrableOn_compact
      (isCompact_closedBall c r) |>.mono_set Metric.ball_subset_closedBall
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpt (x : ℂ) (hx : x ∈ Metric.ball c r) : ‖f x - f c‖ ^ 2 ≤ C ^ 2 * r ^ 2 := by
    have hxq : x ∈ Metric.ball c (R / 4) := Metric.ball_subset_ball hrR hx
    have hcq : c ∈ Metric.ball c (R / 4) := Metric.mem_ball_self (by positivity)
    have hlip := (convex_ball c (R / 4)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hf z (Metric.ball_subset_ball (by linarith : R / 4 ≤ R) hz)).differentiableAt)
      hder hcq hxq
    have hd : ‖x - c‖ ≤ r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using (Metric.mem_ball.mp hx).le
    have hh := hlip.trans (mul_le_mul_of_nonneg_left hd hC)
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hbound : (∫ z in Metric.ball c r, ‖f z - f c‖ ^ 2) ≤
      ∫ _z in Metric.ball c r, C ^ 2 * r ^ 2 := by
    apply integral_mono_ae hfi (integrable_const _)
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hpt x hx
  have hvol : volume.real (Metric.ball c r) = Real.pi * r ^ 2 := by
    rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr, ENNReal.coe_toReal]
    change r ^ 2 * Real.pi = Real.pi * r ^ 2
    ring
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, hvol, hCeq] at hbound
  have heq : Real.pi * r ^ 2 * ((256 / (Real.pi * R ^ 4)) * E * r ^ 2) =
      256 * (r / R) ^ 4 * E := by
    field_simp [Real.pi_ne_zero, hR.ne']
  exact hbound.trans_eq heq

theorem harmonic_integral_derivative_sub_center_sq_le_radius_ratio_pow_four
    {f : ℂ → ℝ} {c : ℂ} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 4)
    (hf : HarmonicOnNhd f (Metric.ball c R)) (a b : ℝ)
    (hi : IntegrableOn (fun z => (fderiv ℝ f z 1 - a) ^ 2 + (fderiv ℝ f z Complex.I - b) ^ 2)
      (Metric.ball c R)) :
    (∫ z in Metric.ball c r,
      (fderiv ℝ f z 1 - fderiv ℝ f c 1) ^ 2 +
        (fderiv ℝ f z Complex.I - fderiv ℝ f c Complex.I) ^ 2) ≤
      256 * (r / R) ^ 4 * ∫ z in Metric.ball c R,
        (fderiv ℝ f z 1 - a) ^ 2 + (fderiv ℝ f z Complex.I - b) ^ 2 := by
  let g : ℂ → ℂ := fun z => (fderiv ℝ f z 1 - a) - Complex.I * (fderiv ℝ f z Complex.I - b)
  have hg : AnalyticOnNhd ℂ g (Metric.ball c R) := by
    have heq : g = (fun z => (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) -
        (a - Complex.I * b)) := by funext z; dsimp only [g]; ring
    rw [heq]
    exact fun z hz => (HarmonicAt.analyticAt_complex_partial (hf z hz)).sub analyticAt_const
  have heq (z : ℂ) : ‖g z‖ ^ 2 = (fderiv ℝ f z 1 - a) ^ 2 +
      (fderiv ℝ f z Complex.I - b) ^ 2 := by
    rw [Complex.sq_norm]
    simp [g, Complex.normSq_apply]
    ring
  have hdiff (z : ℂ) : ‖g z - g c‖ ^ 2 =
      (fderiv ℝ f z 1 - fderiv ℝ f c 1) ^ 2 +
        (fderiv ℝ f z Complex.I - fderiv ℝ f c Complex.I) ^ 2 := by
    rw [Complex.sq_norm]
    simp [g, Complex.normSq_apply]
    ring
  have hgi : IntegrableOn (fun z => ‖g z‖ ^ 2) (Metric.ball c R) := by simpa only [heq] using hi
  simpa only [heq, hdiff] using
    holomorphic_integral_sub_center_sq_le_radius_ratio_pow_four hR hr hrR hg hgi

end DifferentialGeometry.Analysis

end
