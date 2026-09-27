import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball
import DifferentialGeometry.External.DeGiorgi.Poincare
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open Set Filter MeasureTheory InnerProductSpace Real
open scoped Topology

namespace InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem HarmonicOnNhd.integral_polar_circle
    {f : ℂ → F} {x : ℂ} {R r : ℝ}
    (hf : HarmonicOnNhd f (Metric.closedBall x R)) (hr : r ∈ Icc 0 R) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (x - Complex.polarCoord.symm (r, θ))) =
      (2 * Real.pi) • f x := by
  have hdisc : HarmonicOnNhd f (Metric.closedBall x |(-r)|) := by
    simpa only [abs_neg, abs_of_nonneg hr.1] using
      hf.mono (Metric.closedBall_subset_closedBall hr.2)
  have hmean := hdisc.circleAverage_eq
  rw [circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ => f (circleMap x (-r) θ))] at hmean
  have hends : (0 : ℝ) + -Real.pi = -Real.pi := by ring
  have hends' : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [hends, hends'] at hmean
  have hpolar (θ : ℝ) : circleMap x (-r) θ = x - Complex.polarCoord.symm (r, θ) := by
    simp only [circleMap, Complex.polarCoord_symm_apply, Complex.ofReal_neg,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  simp_rw [hpolar] at hmean
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at hmean
  have h := congrArg (fun v : F => (2 * Real.pi) • v) hmean
  simpa only [smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul] using h


theorem HarmonicOnNhd.integral_radial_smul
    {f : ℂ → F} {x : ℂ} {R : ℝ}
    (hf : HarmonicOnNhd f (Metric.closedBall x R))
    {κ : ℂ → ℝ} (hκ : Continuous κ)
    (hκsupport : tsupport κ ⊆ Metric.closedBall (0 : ℂ) R)
    (hκradial : ∀ z : ℂ, κ z = κ (‖z‖ : ℂ)) :
    (∫ z : ℂ, κ z • f (x - z)) = (∫ z : ℂ, κ z) • f x := by
  let H : ℝ × ℝ → F := fun p => p.1 • (κ (Complex.polarCoord.symm p) •
    f (x - Complex.polarCoord.symm p))
  let K : ℝ × ℝ → ℝ := fun p => p.1 * κ (Complex.polarCoord.symm p)
  let A : Set (ℝ × ℝ) := Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  have hAsub : A ⊆ Complex.polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨hr.1, hθ⟩
  have hzero (p : ℝ × ℝ) (hp : p ∈ Complex.polarCoord.target \ A) :
      κ (Complex.polarCoord.symm p) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hrR : p.1 ≤ R := by
      have hnorm := hκsupport hs
      simpa only [Metric.mem_closedBall, dist_zero_right,
        Complex.norm_polarCoord_symm, abs_of_pos (show 0 < p.1 from hp.1.1)] using hnorm
    exact hp.2 ⟨⟨hp.1.1, hrR⟩, hp.1.2⟩
  have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hmap : MapsTo (fun p : ℝ × ℝ => x - Complex.polarCoord.symm p)
      (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi) (Metric.closedBall x R) := by
    intro p hp
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      Complex.norm_polarCoord_symm, abs_of_nonneg hp.1.1] using hp.1.2
  have hHcont : ContinuousOn H (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi) :=
    continuous_fst.continuousOn.smul
      ((hκ.comp hpolar).continuousOn.smul
        (hf.continuousOn.comp (continuous_const.sub hpolar).continuousOn hmap))
  have hKcont : Continuous K := continuous_fst.mul (hκ.comp hpolar)
  have hAbox : A ⊆ Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi :=
    prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self
  have hHint : IntegrableOn H A :=
    (hHcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set hAbox
  have hKint : IntegrableOn K A :=
    (hKcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set hAbox
  have hHpolar : (∫ z : ℂ, κ z • f (x - z)) = ∫ p in A, H p := by
    rw [← Complex.integral_comp_polarCoord_symm]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      Complex.polarCoord.open_target.measurableSet hAsub (fun p hp => by
        rw [hzero p hp, zero_smul, smul_zero])
  have hKpolar : (∫ z : ℂ, κ z) = ∫ p in A, K p := by
    rw [← Complex.integral_comp_polarCoord_symm]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      Complex.polarCoord.open_target.measurableSet hAsub (fun p hp => by
        change p.1 * κ (Complex.polarCoord.symm p) = 0
        rw [hzero p hp, mul_zero])
  have hradial (r θ : ℝ) (hr : 0 ≤ r) :
      κ (Complex.polarCoord.symm (r, θ)) = κ (r : ℂ) := by
    rw [hκradial, Complex.norm_polarCoord_symm, abs_of_nonneg hr]
  rw [hHpolar, hKpolar]
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod H hHint, setIntegral_prod K hKint, ← integral_smul_const]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hH : (fun θ => H (r, θ)) =
      fun θ => (r * κ (r : ℂ)) • f (x - Complex.polarCoord.symm (r, θ)) := by
    funext θ
    dsimp [H]
    rw [hradial r θ hr.1.le, smul_smul]
  have hK : (fun θ => K (r, θ)) = fun _ => r * κ (r : ℂ) := by
    funext θ
    dsimp [K]
    rw [hradial r θ hr.1.le]
  change (∫ θ in Ioo (-Real.pi) Real.pi, H (r, θ)) =
    (∫ θ in Ioo (-Real.pi) Real.pi, K (r, θ)) • f x
  rw [hH, integral_smul, hf.integral_polar_circle ⟨hr.1.le, hr.2⟩, hK]
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos] :
    0 ≤ Real.pi - -Real.pi), smul_eq_mul, smul_smul]
  congr 1
  ring

end InnerProductSpace

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem harmonic_norm_sq_le_integral_norm_sq
    {f : ℂ → F} {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : HarmonicOnNhd f (Metric.closedBall x R)) :
    ‖f x‖ ^ 2 ≤ (4 / (Real.pi * R ^ 2)) * ∫ y in Metric.closedBall x R, ‖f y‖ ^ 2 := by
  let B := Metric.closedBall (0 : ℂ) R
  let κ := ballCutoff (0 : ℂ) (R / 2) R
  have hhalf : R / 2 < R := half_lt_self hR
  have hhalf0 : 0 ≤ R / 2 := by positivity
  have hκ : Continuous κ := (ballCutoff_contDiff (0 : ℂ) (R / 2) R).continuous
  have hκs : tsupport κ ⊆ B := ballCutoff_tsupport_subset_closedBall hhalf0 hhalf
  have hκ0 (z : ℂ) : 0 ≤ κ z := (ballCutoff_mem_Icc 0 (R / 2) R z).1
  have hκ1 (z : ℂ) : κ z ≤ 1 := (ballCutoff_mem_Icc 0 (R / 2) R z).2
  have hrad (z : ℂ) : κ z = κ (‖z‖ : ℂ) := by
    simp only [κ, ballCutoff, ballCutoffArgument, sub_zero, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
  have hmaps : MapsTo (fun z : ℂ => x - z) B (Metric.closedBall x R) := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
      sub_zero, B] using hz
  have hfc : ContinuousOn (fun z : ℂ => f (x - z)) B :=
    hf.continuousOn.comp (continuous_const.sub continuous_id).continuousOn hmaps
  have hki : IntegrableOn κ B := hκ.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hqi : IntegrableOn (fun z : ℂ => ‖f (x - z)‖ ^ 2) B :=
    (hfc.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)
  have hkqi : IntegrableOn (fun z : ℂ => ‖f (x - z)‖ ^ 2 * κ z) B :=
    ((hfc.norm.pow 2).mul hκ.continuousOn).integrableOn_compact (isCompact_closedBall _ _)
  let I := ∫ z in B, κ z
  let J := ∫ z in B, ‖f (x - z)‖ * κ z
  let Q := ∫ z in B, ‖f (x - z)‖ ^ 2
  have hIeq : I = ∫ z, κ z := setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => image_eq_zero_of_notMem_tsupport (fun h => hz (hκs h)))
  have hIlow : Real.pi * (R / 2) ^ 2 ≤ I := by
    have hvol : volume.real (Metric.closedBall (0 : ℂ) (R / 2)) = Real.pi * (R / 2) ^ 2 := by
      rw [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hhalf0, ENNReal.coe_toReal]
      change (R / 2) ^ 2 * Real.pi = Real.pi * (R / 2) ^ 2
      ring
    calc
      _ = ∫ z in Metric.closedBall (0 : ℂ) (R / 2), (1 : ℝ) := by simp [hvol]
      _ = ∫ z in Metric.closedBall (0 : ℂ) (R / 2), κ z := by
        apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
        intro z hz
        exact (ballCutoff_eq_one_of_mem_closedBall hhalf0 hhalf hz).symm
      _ ≤ I := setIntegral_mono_set hki (Eventually.of_forall hκ0)
        (Eventually.of_forall (Metric.closedBall_subset_closedBall hhalf.le))
  have hI : 0 < I := (mul_pos Real.pi_pos (sq_pos_of_pos (half_pos hR))).trans_le hIlow
  have hN : I * ‖f x‖ ≤ J := by
    have hmean := hf.integral_radial_smul hκ hκs hrad
    rw [← hIeq] at hmean
    have heq : (∫ z in B, κ z • f (x - z)) = I • f x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hmean
      · intro z hz
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hκs h)), zero_smul]
    have hh := norm_integral_le_integral_norm
      (f := fun z => κ z • f (x - z)) (μ := volume.restrict B)
    rw [heq, norm_smul, Real.norm_of_nonneg hI.le] at hh
    simpa only [norm_smul, Real.norm_of_nonneg (hκ0 _), mul_comm] using hh
  have hcs : J ^ 2 ≤ I * Q := by
    have hh := DeGiorgi.weighted_power_mean_setIntegral (μ := volume)
      (s := B) Metric.isClosed_closedBall.measurableSet (p := (2 : ℝ)) (by norm_num)
      (f := fun z => ‖f (x - z)‖) (w := κ) (fun z => norm_nonneg _) hκ0
      (hfc.norm.aemeasurable Metric.isClosed_closedBall.measurableSet) hki
      (by simpa only [Real.rpow_two] using hkqi)
    simp only [Real.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hI.le
    exact integral_mono_ae hkqi hqi (Eventually.of_forall fun z =>
      mul_le_of_le_one_right (sq_nonneg _) (hκ1 z))
  have hJs : 0 ≤ J := integral_nonneg (fun z => mul_nonneg (norm_nonneg _) (hκ0 z))
  have hN2 := (sq_le_sq₀ (mul_nonneg hI.le (norm_nonneg _)) hJs).mpr hN
  have hIQ : I * ‖f x‖ ^ 2 ≤ Q := by
    apply (mul_le_mul_iff_of_pos_left hI).mp
    nlinarith
  have hfinal : Real.pi * (R / 2) ^ 2 * ‖f x‖ ^ 2 ≤ Q :=
    (mul_le_mul_of_nonneg_right hIlow (sq_nonneg _)).trans hIQ
  have hQ : Q = ∫ y in Metric.closedBall x R, ‖f y‖ ^ 2 := by
    have hp : (fun z : ℂ => x - z) ⁻¹' Metric.closedBall x R = B := by
      ext z
      simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left,
        norm_neg, B, sub_zero]
    have hm := (volume : Measure ℂ).measurePreserving_sub_left x
    have hh := hm.setIntegral_preimage_emb
      ((Homeomorph.subLeft x).toMeasurableEquiv.measurableEmbedding) (fun y => ‖f y‖ ^ 2)
      (Metric.closedBall x R)
    rwa [hp] at hh
  rw [hQ] at hfinal
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos hR))).mpr
  nlinarith

end DifferentialGeometry.Analysis

end
