import DifferentialGeometry.Analysis.Integration.PolarAnnulus
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous.Energy
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DifferentialGeometry.Topology.MetricSpace.LipschitzExtension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import DifferentialGeometry.Analysis.Integration.Integral.ExhaustingBalls

noncomputable section

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem continuous_circle_radius_angle :
    Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi)) := by
  unfold circleMap
  fun_prop

private theorem radial_displacement_sq_le
    {f : ℂ → F} (hf : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (θ : ℝ) :
    ‖f (circleMap 0 a θ) - f (circleMap 0 b θ)‖ ^ 2 ≤
      (b - a) * ∫ ρ in Icc a b, ‖fderiv ℝ f (circleMap 0 ρ θ)‖ ^ 2 := by
  let c (ρ : ℝ) := circleMap 0 ρ θ
  let w : ℂ := Complex.exp (θ * Complex.I)
  have hw : ‖w‖ = 1 := by simp [w]
  have hc (ρ : ℝ) : HasDerivAt c w ρ := by
    have h := (hasDerivAt_id ρ).smul_const w
    simpa only [c, w, circleMap_zero, Complex.real_smul, id_eq, Complex.ofReal_one, one_mul] using h
  have hcD (ρ : ℝ) (hρ : ρ ∈ Icc a b) : c ρ ∈ ball (0 : ℂ) 1 := by
    dsimp only [c]
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (ha.trans_le hρ.1)]
    exact hρ.2.trans_lt hb
  have hdf := hf.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hdc : ContinuousOn (fun ρ => fderiv ℝ f (c ρ)) (Icc a b) :=
    hdf.comp (fun ρ _ => (hc ρ).continuousAt.continuousWithinAt) hcD
  have hd (ρ : ℝ) (hρ : ρ ∈ Icc a b) :
      HasDerivAt (f ∘ c) (fderiv ℝ f (c ρ) w) ρ :=
    ((hf.differentiableOn (by norm_num)).differentiableAt
      (isOpen_ball.mem_nhds (hcD ρ hρ))).hasFDerivAt.comp_hasDerivAt
      ρ (hc ρ)
  have hi : IntervalIntegrable (fun ρ => fderiv ℝ f (c ρ) w) volume a b :=
    (hdc.clm_apply continuousOn_const).intervalIntegrable_of_Icc hab
  have hnormc : ContinuousOn (fun ρ => ‖fderiv ℝ f (c ρ)‖) (Icc a b) :=
    (@continuous_norm (ℂ →L[ℝ] F) inferInstance).comp_continuousOn hdc
  have heq : (∫ ρ in a..b, fderiv ℝ f (c ρ) w) = f (c b) - f (c a) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun ρ hρ => hd ρ (by simpa only [uIcc_of_le hab] using hρ)) hi
  have hnorm : ‖f (c b) - f (c a)‖ ≤ ∫ ρ in a..b, ‖fderiv ℝ f (c ρ)‖ := by
    rw [← heq]
    apply intervalIntegral.norm_integral_le_of_norm_le hab _
      (hnormc.intervalIntegrable_of_Icc hab)
    exact Eventually.of_forall fun ρ _ => by
      simpa only [hw, mul_one] using (fderiv ℝ f (c ρ)).le_opNorm w
  have hm : MemLp (fun ρ => ‖fderiv ℝ f (c ρ)‖) 2 (volume.restrict (Icc a b)) := by
    obtain ⟨R, hR⟩ := (isCompact_Icc.image_of_continuousOn hnormc).isBounded.exists_norm_le
    apply MemLp.of_bound (hnormc.integrableOn_Icc.aestronglyMeasurable) R
    filter_upwards [ae_restrict_mem measurableSet_Icc] with ρ hρ
    exact hR _ (mem_image_of_mem _ hρ)
  have hcs := integral_sq_le_measure_mul_integral_sq hm
  have hmeasure : (volume.restrict (Icc a b)).real univ = b - a := by
    simp [Measure.real, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hmeasure] at hcs
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hnorm
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [c, norm_sub_rev] using hs.trans hcs

private theorem integral_radial_displacement_sq_le_interior
    {f : ℂ → F} (hf : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    {a b : ℝ} (ha : (1 / 2 : ℝ) < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ t in Icc (0 : ℝ) 1,
      ‖f (circleMap 0 a (2 * Real.pi * t - Real.pi)) -
        f (circleMap 0 b (2 * Real.pi * t - Real.pi))‖ ^ 2) ≤
      2 * (b - a) * ∫ z in {z : ℂ | ‖z‖ ∈ Icc a b}, ‖fderiv ℝ f z‖ ^ 2 := by
  have ha0 : 0 < a := by linarith
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let c (p : ℝ × ℝ) := circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi)
  let Q (p : ℝ × ℝ) := ‖fderiv ℝ f (c p)‖ ^ 2
  let W (p : ℝ × ℝ) := p.1 * Q p
  let S := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hcD : MapsTo c S (ball (0 : ℂ) 1) := by
    intro p hp
    dsimp only [c]
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (ha0.trans_le hp.1.1)]
    exact hp.1.2.trans_lt hb
  have hdc : ContinuousOn (fun p => fderiv ℝ f (c p)) S :=
    (hf.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp
      continuous_circle_radius_angle.continuousOn hcD
  have hQc : ContinuousOn Q S :=
    ((@continuous_norm (ℂ →L[ℝ] F) inferInstance).comp_continuousOn hdc).pow 2
  have hWc : ContinuousOn W S := continuous_fst.continuousOn.mul hQc
  have hQi : Integrable Q (μ.prod ν) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hQc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hWi : Integrable W (μ.prod ν) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hWc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hgradc : ContinuousOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (closedBall (0 : ℂ) b) := by
    apply ((@continuous_norm (ℂ →L[ℝ] F) inferInstance).comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)).pow 2 |>.mono
    intro z hz
    exact lt_of_le_of_lt hz hb
  obtain ⟨R, hR⟩ := ((isCompact_closedBall (0 : ℂ) b).image_of_continuousOn hgradc).isBounded
    |>.exists_norm_le
  have hgradm : Measurable (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    (measurable_fderiv ℝ f).norm.pow_const 2
  have hpolar := integral_annulus_eq_integral_normalized_polar_of_bounded hgradm ha0
    (fun z hz => hR _ (mem_image_of_mem _ (show z ∈ closedBall (0 : ℂ) b from by
      simpa only [mem_closedBall, dist_zero_right] using hz.2)))
  have hp₀ (ρ θ : ℝ) : Complex.polarCoord.symm (ρ, θ) = circleMap 0 ρ θ := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  have hp (p : ℝ × ℝ) :
      Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi) = c p :=
    hp₀ p.1 (2 * Real.pi * p.2 - Real.pi)
  simp only [hp] at hpolar
  have hE : (∫ z in {z : ℂ | ‖z‖ ∈ Icc a b}, ‖fderiv ℝ f z‖ ^ 2) =
      (2 * Real.pi) * ∫ p, W p ∂μ.prod ν := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hpolar
  have hQW : (∫ p, Q p ∂μ.prod ν) ≤ 2 * ∫ p, W p ∂μ.prod ν := by
    rw [← integral_const_mul]
    apply integral_mono_ae hQi (hWi.const_mul 2)
    have hrad : ∀ᵐ p ∂μ.prod ν, p.1 ∈ Icc a b :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hrad] with p hp
    dsimp only [W]
    nlinarith [sq_nonneg ‖fderiv ℝ f (c p)‖, hp.1]
  have hW0 : 0 ≤ ∫ p, W p ∂μ.prod ν := by
    have hrad : ∀ᵐ p ∂μ.prod ν, p.1 ∈ Icc a b :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    apply integral_nonneg_of_ae
    filter_upwards [hrad] with p hp
    exact mul_nonneg (ha0.le.trans hp.1) (sq_nonneg _)
  have hQE : (∫ p, Q p ∂μ.prod ν) ≤
      2 * ∫ z in {z : ℂ | ‖z‖ ∈ Icc a b}, ‖fderiv ℝ f z‖ ^ 2 := by
    rw [hE]
    nlinarith [Real.pi_gt_three]
  have hci (ρ : ℝ) (hρ : ρ ∈ Icc a b) :
      ContinuousOn (fun t => f (c (ρ, t))) (Icc (0 : ℝ) 1) := by
    apply hf.continuousOn.comp
    · exact (continuous_circle_radius_angle.comp
        (continuous_const.prodMk continuous_id)).continuousOn
    · intro t ht
      exact hcD ⟨hρ, ht⟩
  have hdiffi : Integrable (fun t => ‖f (c (a, t)) - f (c (b, t))‖ ^ 2) ν :=
    (((hci a ⟨le_rfl, hab⟩).sub (hci b ⟨hab, le_rfl⟩)).norm.pow 2).integrableOn_Icc
  calc
    _ ≤ ∫ t, (b - a) * ∫ ρ, Q (ρ, t) ∂μ ∂ν := by
      apply integral_mono_ae hdiffi (hQi.integral_prod_right.const_mul (b - a))
      exact Eventually.of_forall fun t => radial_displacement_sq_le hf ha0 hab hb _
    _ = (b - a) * ∫ p, Q p ∂μ.prod ν := by
      rw [integral_const_mul, ← integral_prod_symm _ hQi]
    _ ≤ 2 * (b - a) * ∫ z in {z : ℂ | ‖z‖ ∈ Icc a b}, ‖fderiv ℝ f z‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hQE (sub_nonneg.mpr hab)]

theorem integral_norm_radial_boundary_sub_sq_le
    {f : ℂ → F} (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfs : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball (0 : ℂ) 1))
    {a : ℝ} (ha : (1 / 2 : ℝ) < a) (ha1 : a < 1) :
    (∫ t in Icc (0 : ℝ) 1,
      ‖f (circleMap 0 a (2 * Real.pi * t - Real.pi)) -
        f (circleMap 0 1 (2 * Real.pi * t - Real.pi))‖ ^ 2) ≤
      2 * (1 - a) * ∫ z in {z : ℂ | ‖z‖ ∈ Icc a 1}, ‖fderiv ℝ f z‖ ^ 2 := by
  have ha0 : 0 < a := by linarith
  let b (n : ℕ) := 1 - (1 - a) * (1 / 2 : ℝ) ^ (n + 1)
  have hab (n : ℕ) : a ≤ b n := by
    have hp : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [b]
    nlinarith [mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr ha1.le)]
  have hb1 (n : ℕ) : b n < 1 := by
    dsimp only [b]
    exact sub_lt_self _ (mul_pos (sub_pos.mpr ha1) (pow_pos (by norm_num) _))
  have hblim : Tendsto b atTop (𝓝 1) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub (hp.const_mul (1 - a))
    simpa only [b, pow_succ, zero_mul, mul_zero, sub_zero] using hh
  let c (ρ t : ℝ) := circleMap 0 ρ (2 * Real.pi * t - Real.pi)
  have hcmem (ρ t : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) : c ρ t ∈ closedBall (0 : ℂ) 1 := by
    simp only [c, mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hρ.1, hρ.2]
  have hcc (ρ : ℝ) : Continuous (c ρ) := by
    exact continuous_circle_radius_angle.comp (continuous_const.prodMk continuous_id)
  have hfc (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) : Continuous (fun t => f (c ρ t)) := by
    exact hf.comp_continuous (hcc ρ) (fun t => hcmem ρ t hρ)
  let Q (n : ℕ) (t : ℝ) := ‖f (c a t) - f (c (b n) t)‖ ^ 2
  let Q₀ (t : ℝ) := ‖f (c a t) - f (c 1 t)‖ ^ 2
  have hQc (n : ℕ) : Continuous (Q n) :=
    ((hfc a ⟨ha0.le, ha1.le⟩).sub (hfc (b n) ⟨ha0.le.trans (hab n), (hb1 n).le⟩)).norm.pow 2
  obtain ⟨R, hR⟩ := ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hf).isBounded
    |>.exists_norm_le
  have hnorm (ρ t : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) : ‖f (c ρ t)‖ ≤ R :=
    hR _ (mem_image_of_mem f (hcmem ρ t hρ))
  have hQbound (n : ℕ) : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ‖Q n t‖ ≤ (2 * R) ^ 2 := by
    apply Eventually.of_forall
    intro t
    dsimp only [Q]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by
      linarith [hnorm a t ⟨ha0.le, ha1.le⟩,
        hnorm (b n) t ⟨ha0.le.trans (hab n), (hb1 n).le⟩])
  have hQlim : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      Tendsto (fun n => Q n t) atTop (𝓝 (Q₀ t)) := by
    apply Eventually.of_forall
    intro t
    have hradius : Continuous (fun ρ : ℝ => c ρ t) :=
      continuous_circle_radius_angle.comp (continuous_id.prodMk continuous_const)
    have hcir : Tendsto (fun n => c (b n) t) atTop (𝓝 (c 1 t)) :=
      (hradius.tendsto 1).comp hblim
    have hwithin : Tendsto (fun n => c (b n) t) atTop
        (𝓝[closedBall (0 : ℂ) 1] (c 1 t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hcir, Eventually.of_forall fun n =>
        hcmem (b n) t ⟨ha0.le.trans (hab n), (hb1 n).le⟩⟩
    have hfv := (hf (c 1 t) (hcmem 1 t ⟨zero_le_one, le_rfl⟩)).tendsto.comp hwithin
    exact (((tendsto_const_nhds (x := f (c a t))).sub hfv).norm).pow 2
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (2 * R) ^ 2)
    (fun n => (hQc n).aestronglyMeasurable) (integrableOn_const (by simp)) hQbound hQlim
  have hno : ∀ᵐ z : ℂ, z ∉ sphere (0 : ℂ) 1 := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : ℂ) 1 using 1
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, not_not]
  have hEi : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) {z : ℂ | ‖z‖ ∈ Icc a 1} := by
    apply hE.mono_set_ae
    change ∀ᵐ z : ℂ, ‖z‖ ∈ Icc a 1 → z ∈ ball (0 : ℂ) 1
    filter_upwards [hno] with z hz
    intro hza
    have hne : ‖z‖ ≠ 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_ne hza.2 hne)
  have hE0 : 0 ≤ ∫ z in {z : ℂ | ‖z‖ ∈ Icc a 1}, ‖fderiv ℝ f z‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have he := integral_radial_displacement_sq_le_interior hfs ha (hab n) (hb1 n)
  have hsub : {z : ℂ | ‖z‖ ∈ Icc a (b n)} ⊆ {z : ℂ | ‖z‖ ∈ Icc a 1} := by
    intro z hz
    exact ⟨hz.1, hz.2.trans (hb1 n).le⟩
  have hmono : (∫ z in {z : ℂ | ‖z‖ ∈ Icc a (b n)}, ‖fderiv ℝ f z‖ ^ 2) ≤
      ∫ z in {z : ℂ | ‖z‖ ∈ Icc a 1}, ‖fderiv ℝ f z‖ ^ 2 :=
    setIntegral_mono_set hEi (Eventually.of_forall fun _ => sq_nonneg _) hsub.eventuallyLE
  exact he.trans ((mul_le_mul_of_nonneg_left hmono (by nlinarith [hab n])).trans
    (mul_le_mul_of_nonneg_right (by nlinarith [hb1 n]) hE0))

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_inner_circle_energy_le_collar_energy
    {f : ℂ → F} (hf : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball (0 : ℂ) 1))
    {h : ℝ} (hh : 0 < h) (hhhalf : h < 1 / 2) :
    ∃ a ∈ Icc (1 - h) (1 - h / 2),
      h * (∫ t in Icc (0 : ℝ) 1,
        ‖deriv (fun t => f (circleMap 0 a (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤
        4 * Real.pi * ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) 1}, ‖fderiv ℝ f z‖ ^ 2 := by
  let R := 1 - h / 4
  have hR0 : 0 < R := by dsimp only [R]; linarith
  have hR1 : R < 1 := by dsimp only [R]; linarith
  have hRbound : 1 - h / 2 < R := by dsimp only [R]; linarith
  have hlo : 0 < 1 - h := by linarith
  have horder : 1 - h < 1 - h / 2 := by linarith
  have hsub : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hR1
  obtain ⟨L, hL⟩ := (hf.mono hsub).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : ℂ) R) (isCompact_closedBall (0 : ℂ) R)
  obtain ⟨g, K, hg, hfg⟩ := hL.exists_lipschitz_extension
  have hderiv {z : ℂ} (hz : ‖z‖ < R) : fderiv ℝ f z = fderiv ℝ g z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds
      (show z ∈ ball (0 : ℂ) R from by simpa only [mem_ball, dist_zero_right] using hz)] with y hy
    exact hfg (ball_subset_closedBall hy)
  have hloop {a : ℝ} (ha : a ∈ Icc (1 - h) (1 - h / 2)) :
      (fun t : ℝ => f (circleMap 0 a (2 * Real.pi * t - Real.pi))) =
        (fun t : ℝ => g (circleMap 0 a (2 * Real.pi * t - Real.pi))) := by
    funext t
    apply hfg
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_pos (hlo.trans_le ha.1)]
    exact ha.2.trans hRbound.le
  let Eg : ℝ → ℝ := fun a => ∫ t in Icc (0 : ℝ) 1,
    ‖deriv (fun t => g (circleMap 0 a (2 * Real.pi * t - Real.pi))) t‖ ^ 2
  have hEg : IntegrableOn Eg (Icc (1 - h) (1 - h / 2)) :=
    integrableOn_integral_norm_sq_deriv_circleMap hg hlo horder.le
  have hmeasure : volume (Icc (1 - h) (1 - h / 2)) ≠ 0 := by
    rw [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  obtain ⟨a, ha, hEa⟩ := exists_le_setAverage hmeasure isCompact_Icc.measure_ne_top hEg
  have hlength : (1 - h / 2) - (1 - h) = h / 2 := by ring
  have hmean : (⨍ a in Icc (1 - h) (1 - h / 2), Eg a) =
      (h / 2)⁻¹ * ∫ a in Icc (1 - h) (1 - h / 2), Eg a := by
    rw [setAverage_eq]
    simp only [Measure.real, Real.volume_Icc, hlength, ENNReal.toReal_ofReal (half_pos hh).le,
      smul_eq_mul]
  rw [hmean] at hEa
  have hchosen : h * Eg a ≤ 2 * ∫ a in Icc (1 - h) (1 - h / 2), Eg a := by
    have hx := mul_le_mul_of_nonneg_left hEa hh.le
    apply hx.trans_eq
    field_simp
  have hpolar : (∫ a in Icc (1 - h) (1 - h / 2), Eg a) ≤
      (2 * Real.pi * (1 - h / 2)) *
        ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) (1 - h / 2)}, ‖fderiv ℝ g z‖ ^ 2 :=
    integral_norm_sq_deriv_circleMap_radial_le hg hlo horder.le
  have hannulus :
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) (1 - h / 2)}, ‖fderiv ℝ g z‖ ^ 2) =
        ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) (1 - h / 2)}, ‖fderiv ℝ f z‖ ^ 2 := by
    apply setIntegral_congr_fun
      ((isClosed_Icc.preimage continuous_norm).measurableSet)
    intro z hz
    change ‖fderiv ℝ g z‖ ^ 2 = ‖fderiv ℝ f z‖ ^ 2
    rw [hderiv (hz.2.trans_lt hRbound)]
  rw [hannulus] at hpolar
  have hzero : ∀ᵐ z : ℂ ∂volume, z ∉ sphere (0 : ℂ) 1 := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : ℂ) 1 using 1
    congr 1
    ext z
    simp only [mem_ofPred_eq, not_not]
  have hcollarInt : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2)
      {z : ℂ | ‖z‖ ∈ Icc (1 - h) 1} := by
    apply hE.mono_set_ae
    filter_upwards [hzero] with z hz hzc
    change dist z 0 < 1
    rw [dist_zero_right]
    have hne : ‖z‖ ≠ 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    exact lt_of_le_of_ne hzc.2 hne
  have hmono :
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) (1 - h / 2)}, ‖fderiv ℝ f z‖ ^ 2) ≤
        ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) 1}, ‖fderiv ℝ f z‖ ^ 2 :=
    setIntegral_mono_set hcollarInt (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun z hz => ⟨hz.1, hz.2.trans (by linarith)⟩)
  have hcollar0 : 0 ≤ ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) 1}, ‖fderiv ℝ f z‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  refine ⟨a, ha, ?_⟩
  rw [hloop ha]
  change h * Eg a ≤ _
  have hpolarmul := mul_le_mul_of_nonneg_left hpolar (by norm_num : (0 : ℝ) ≤ 2)
  have hcoeff : 0 ≤ 4 * Real.pi * (1 - h / 2) :=
    mul_nonneg (by positivity) (by linarith)
  have hmonomul := mul_le_mul_of_nonneg_left hmono hcoeff
  have hRle : 4 * Real.pi * (1 - h / 2) ≤ 4 * Real.pi := by
    nlinarith [Real.pi_pos]
  exact hchosen.trans (hpolarmul.trans (by
    calc
      _ = (4 * Real.pi * (1 - h / 2)) *
          (∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) (1 - h / 2)}, ‖fderiv ℝ f z‖ ^ 2) := by ring
      _ ≤ (4 * Real.pi * (1 - h / 2)) *
          (∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h) 1}, ‖fderiv ℝ f z‖ ^ 2) := hmonomul
      _ ≤ _ := mul_le_mul_of_nonneg_right hRle hcollar0))

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_inner_radii_tendsto_scaled_boundary_rates
    {f : ℂ → F} (hf : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hfs : ContDiffOn ℝ 1 f (ball (0 : ℂ) 1))
    (hE : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) (ball (0 : ℂ) 1))
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n < 1 / 2)
    (hh0 : Tendsto h atTop (𝓝 0))
    (b : ℕ → ℝ → F) (Kb : ℕ → ℝ≥0) (hb : ∀ n, LipschitzWith (Kb n) (b n))
    (hgap : Tendsto (fun n => (h n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖f (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - b n t‖ ^ 2) atTop (𝓝 0))
    (hder : Tendsto (fun n => h n * ∫ t in Icc (0 : ℝ) 1, ‖deriv (b n) t‖ ^ 2)
      atTop (𝓝 0)) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ Icc (1 - h n) (1 - h n / 2)) ∧
      Tendsto a atTop (𝓝 1) ∧
      Tendsto (fun n => (1 - a n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
        ‖f (circleMap 0 (a n) (2 * Real.pi * t - Real.pi)) - b n t‖ ^ 2)
        atTop (𝓝 0) ∧
      Tendsto (fun n => (1 - a n) * ∫ t in Icc (0 : ℝ) 1,
        ‖deriv (fun t => f (circleMap 0 (a n) (2 * Real.pi * t - Real.pi))) t‖ ^ 2 +
          ‖deriv (b n) t‖ ^ 2) atTop (𝓝 0) := by
  let e (z : ℂ) := ‖fderiv ℝ f z‖ ^ 2
  have hno : ∀ᵐ z : ℂ ∂volume, z ∉ sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) 1)
  have hEc : IntegrableOn e (closedBall (0 : ℂ) 1) := by
    apply hE.mono_set_ae
    filter_upwards [hno] with z hz hzc
    exact lt_of_le_of_ne hzc hz
  let E (n : ℕ) := ∫ z in {z : ℂ | ‖z‖ ∈ Icc (1 - h n) 1}, e z
  have hE0 (n : ℕ) : 0 ≤ E n := integral_nonneg fun z => sq_nonneg _
  have hElim : Tendsto E atTop (𝓝 0) := by
    have hr : Tendsto (fun n => 1 - h n) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hh0
    have hlim := tendsto_integral_closedBall_sdiff_of_tendsto_radius hEc
      (Measure.addHaar_sphere volume (0 : ℂ) 1) hr
    simpa only [integral_closedBall_sdiff_eq_integral_norm_annulus_complex,
      dist_zero_right, E] using hlim
  choose a ha hchosen using fun n => exists_inner_circle_energy_le_collar_energy hfs hE
    (hh n).1 (hh n).2
  have ha0 (n : ℕ) : 0 < a n := by linarith [(ha n).1, (hh n).2]
  have ha1 (n : ℕ) : a n < 1 := by linarith [(ha n).2, (hh n).1]
  have hahalf (n : ℕ) : 1 / 2 < a n := by linarith [(ha n).1, (hh n).2]
  have halim : Tendsto a atTop (𝓝 1) := by
    have hlo : Tendsto (fun n => 1 - h n) atTop (𝓝 1) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub hh0
    have hhi : Tendsto (fun n => 1 - h n / 2) atTop (𝓝 1) := by
      simpa only [zero_div, sub_zero] using tendsto_const_nhds.sub (hh0.div_const 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => (ha n).1) (fun n => (ha n).2)
  let width (n : ℕ) := 1 - a n
  have hw0 (n : ℕ) : 0 < width n := sub_pos.mpr (ha1 n)
  have hwh (n : ℕ) : width n ≤ h n := by dsimp only [width]; linarith [(ha n).1]
  have hhw (n : ℕ) : h n / 2 ≤ width n := by dsimp only [width]; linarith [(ha n).2]
  let inn (n : ℕ) (t : ℝ) := f (circleMap 0 (a n) (2 * Real.pi * t - Real.pi))
  let out (t : ℝ) := f (circleMap 0 1 (2 * Real.pi * t - Real.pi))
  let gap (n : ℕ) := ∫ t in Icc (0 : ℝ) 1, ‖out t - b n t‖ ^ 2
  have hcont (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
      Continuous (fun t => f (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) := by
    apply hf.comp_continuous (by unfold circleMap; fun_prop)
    intro t
    rw [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hρ.1]
    exact hρ.2
  have hrad (n : ℕ) :
      (width n)⁻¹ * (∫ t in Icc (0 : ℝ) 1, ‖inn n t - out t‖ ^ 2) ≤ 2 * E n := by
    have hbound := integral_norm_radial_boundary_sub_sq_le hf hfs hE (hahalf n) (ha1 n)
    have hmono : (∫ z in {z : ℂ | ‖z‖ ∈ Icc (a n) 1}, e z) ≤ E n := by
      apply setIntegral_mono_set (t := {z : ℂ | ‖z‖ ∈ Icc (1 - h n) 1})
        (hEc.mono_set (fun z hz => by
        simpa only [mem_closedBall, dist_zero_right] using hz.2))
        (Eventually.of_forall fun z => sq_nonneg _) (Eventually.of_forall fun z hz => ⟨
          (ha n).1.trans hz.1, hz.2⟩)
    have hmul := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (hw0 n).le)
    have hwne : width n ≠ 0 := (hw0 n).ne'
    change (width n)⁻¹ * _ ≤ _
    calc
      _ ≤ (width n)⁻¹ * (2 * width n * ∫ z in {z : ℂ | ‖z‖ ∈ Icc (a n) 1}, e z) := hmul
      _ = 2 * ∫ z in {z : ℂ | ‖z‖ ∈ Icc (a n) 1}, e z := by field_simp
      _ ≤ 2 * E n := mul_le_mul_of_nonneg_left hmono (by norm_num)
  have hgap0 (n : ℕ) : 0 ≤ gap n := integral_nonneg fun t => sq_nonneg _
  have hgaplim : Tendsto (fun n => (width n)⁻¹ * ∫ t in Icc (0 : ℝ) 1,
      ‖inn n t - b n t‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (inv_nonneg.mpr (hw0 n).le)
      (integral_nonneg fun t => sq_nonneg _)) ?_
      (by simpa only [mul_zero, add_zero] using (hElim.const_mul 4).add (hgap.const_mul 4))
    intro n
    have hi : IntegrableOn (fun t => ‖inn n t - b n t‖ ^ 2) (Icc (0 : ℝ) 1) :=
      (((hcont (a n) ⟨(ha0 n).le, (ha1 n).le⟩).sub (hb n).continuous).norm.pow 2).integrableOn_Icc
    have hir : IntegrableOn (fun t => ‖inn n t - out t‖ ^ 2) (Icc (0 : ℝ) 1) :=
      (((hcont (a n) ⟨(ha0 n).le, (ha1 n).le⟩).sub
        (hcont 1 ⟨zero_le_one, le_rfl⟩)).norm.pow 2).integrableOn_Icc
    have hob : IntegrableOn (fun t => ‖out t - b n t‖ ^ 2) (Icc (0 : ℝ) 1) :=
      (((hcont 1 ⟨zero_le_one, le_rfl⟩).sub (hb n).continuous).norm.pow 2).integrableOn_Icc
    have htri : (∫ t in Icc (0 : ℝ) 1, ‖inn n t - b n t‖ ^ 2) ≤
        2 * (∫ t in Icc (0 : ℝ) 1, ‖inn n t - out t‖ ^ 2) + 2 * gap n := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (hir.const_mul 2) (hob.const_mul 2)]
      apply integral_mono hi ((hir.const_mul 2).add (hob.const_mul 2))
      intro t
      have ht := norm_sub_le_norm_sub_add_norm_sub (inn n t) (out t) (b n t)
      change ‖inn n t - b n t‖ ^ 2 ≤ 2 * ‖inn n t - out t‖ ^ 2 + 2 * ‖out t - b n t‖ ^ 2
      have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
      nlinarith [sq_nonneg (‖inn n t - out t‖ - ‖out t - b n t‖)]
    have hinv : (width n)⁻¹ ≤ 2 * (h n)⁻¹ := by
      calc
        _ ≤ (h n / 2)⁻¹ := inv_anti₀ (half_pos (hh n).1) (hhw n)
        _ = 2 * (h n)⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have hm := mul_le_mul_of_nonneg_left htri (inv_nonneg.mpr (hw0 n).le)
    have hg := mul_le_mul_of_nonneg_right hinv (hgap0 n)
    nlinarith [hrad n]
  have hinnerlim : Tendsto (fun n => width n * ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (inn n) t‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (hw0 n).le (integral_nonneg fun t => sq_nonneg _)) ?_
      (by simpa only [mul_zero] using hElim.const_mul (4 * Real.pi))
    intro n
    exact (mul_le_mul_of_nonneg_right (hwh n) (integral_nonneg fun t => sq_nonneg _)).trans
      (hchosen n)
  have houterlim : Tendsto (fun n => width n * ∫ t in Icc (0 : ℝ) 1,
      ‖deriv (b n) t‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => mul_nonneg (hw0 n).le (integral_nonneg fun t => sq_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (hwh n) (integral_nonneg fun t => sq_nonneg _)) hder
  refine ⟨a, ha, halim, hgaplim, ?_⟩
  have hinni (n : ℕ) : IntegrableOn (fun t => ‖deriv (inn n) t‖ ^ 2) (Icc (0 : ℝ) 1) := by
    have hsm : ContDiff ℝ 1 (inn n) := by
      have hθ : ContDiff ℝ 1 (fun t : ℝ => (2 * Real.pi * t - Real.pi)) := by fun_prop
      have hcomplex : ContDiff ℝ 1 (fun t : ℝ =>
          (↑(2 * Real.pi * t - Real.pi) : ℂ)) := Complex.ofRealCLM.contDiff.comp hθ
      have hc : ContDiff ℝ 1 (fun t : ℝ => circleMap 0 (a n) (2 * Real.pi * t - Real.pi)) := by
        simpa only [circleMap, zero_add] using
          contDiff_const.mul (hcomplex.mul contDiff_const).cexp
      apply hfs.comp_contDiff hc
      intro t
      rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (ha0 n)]
      exact ha1 n
    exact (hsm.continuous_deriv le_rfl).norm.pow 2 |>.integrableOn_Icc
  have hbni (n : ℕ) : IntegrableOn (fun t => ‖deriv (b n) t‖ ^ 2) (Icc (0 : ℝ) 1) := by
    have hm : MemLp (deriv (b n)) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
      MemLp.of_bound (aestronglyMeasurable_deriv _ _) (Kb n)
        (Eventually.of_forall fun t => norm_deriv_le_of_lipschitz (hb n))
    exact hm.norm.integrable_sq
  have ht := hinnerlim.add houterlim
  simp only [add_zero] at ht
  convert ht using 1
  funext n
  rw [integral_add (hinni n) (hbni n), mul_add]

end DifferentialGeometry.Analysis

end
