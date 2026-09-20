import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Analysis.Calculus.Derivative.DifferentialComparison
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.UniformConvergence

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem memLp_Icc_of_lipschitz {f : ℝ → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : MemLp f 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  let : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  obtain ⟨R, hR⟩ := (isCompact_Icc.image hf.continuous).isBounded.exists_norm_le
  apply MemLp.of_bound hf.continuous.aestronglyMeasurable R
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hR (f x) (mem_image_of_mem f hx)

private theorem memLp_deriv_Icc_of_lipschitz {f : ℝ → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : MemLp (deriv f) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  let : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact MemLp.of_bound (aestronglyMeasurable_deriv f _) K
    (Eventually.of_forall fun x => norm_deriv_le_of_lipschitz hf)

private theorem norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz_real
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖f x‖ ^ 2 ≤ (∫ t in Icc (0 : ℝ) 1, ‖f t‖ ^ 2) +
      2 * Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let q (t : ℝ) := ‖f t‖ ^ 2
  let p (t : ℝ) := ‖f t‖ * ‖deriv f t‖
  have hfm : MemLp f 2 μ := memLp_Icc_of_lipschitz hf
  have hdfm : MemLp (deriv f) 2 μ := memLp_deriv_Icc_of_lipschitz hf
  have hp : Integrable p μ := hfm.norm.integrable_mul hdfm.norm
  have hqm : Integrable q μ :=
    (memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable).mp hfm
  have hqd : deriv q =ᵐ[volume] fun t => 2 * inner ℝ (f t) (deriv f t) := by
    filter_upwards [hf.ae_differentiableAt_real] with t ht
    exact ht.hasDerivAt.norm_sq.deriv
  have hholder : (∫ t, p t ∂μ) ≤
      Real.sqrt (∫ t, q t ∂μ) * Real.sqrt (∫ t, ‖deriv f t‖ ^ 2 ∂μ) := by
    have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hfm
    have hdf' : MemLp (deriv f) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hdfm
    have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hdf'
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      q x ≤ q y + 2 * ∫ t, p t ∂μ := by
    have hnormac : AbsolutelyContinuousOnInterval (fun t => ‖f t‖) y x :=
      (lipschitzWith_one_norm.comp hf).lipschitzOnWith.absolutelyContinuousOnInterval
    have hqac : AbsolutelyContinuousOnInterval q y x := by
      convert hnormac.mul hnormac using 1
      funext t
      simp only [q, pow_two, Pi.mul_apply]
    have heq : q x - q y = ∫ t in y..x, 2 * inner ℝ (f t) (deriv f t) := by
      rw [← hqac.integral_deriv_eq_sub]
      exact intervalIntegral.integral_congr_ae_restrict (ae_restrict_of_ae hqd)
    have hsub : uIoc y x ⊆ Icc (0 : ℝ) 1 :=
      uIoc_subset_uIcc.trans (uIcc_subset_Icc hy hx)
    have hp' : IntegrableOn p (uIoc y x) :=
      (show IntegrableOn p (Icc (0 : ℝ) 1) volume from hp).mono_set hsub
    have hi : IntegrableOn (fun t => 2 * inner ℝ (f t) (deriv f t)) (uIoc y x) := by
      apply (hp'.const_mul 2).mono'
        (((hfm.aestronglyMeasurable.inner hdfm.aestronglyMeasurable).const_mul 2).mono_measure
          (Measure.restrict_mono hsub le_rfl))
      exact Eventually.of_forall fun t => by
        rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    have hnorm : |q x - q y| ≤ 2 * ∫ t, p t ∂μ := by
      rw [heq, ← Real.norm_eq_abs]
      calc
        _ ≤ ∫ t in uIoc y x, ‖2 * inner ℝ (f t) (deriv f t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ t in uIoc y x, 2 * p t := by
          apply integral_mono_ae hi.norm (hp'.const_mul 2)
          exact Eventually.of_forall fun t => by
            change ‖2 * inner ℝ (f t) (deriv f t)‖ ≤ 2 * (‖f t‖ * ‖deriv f t‖)
            rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
        _ = 2 * ∫ t in uIoc y x, p t := integral_const_mul _ _
        _ ≤ 2 * ∫ t, p t ∂μ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact setIntegral_mono_set hp
            (Eventually.of_forall fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            hsub.eventuallyLE
    linarith [le_abs_self (q x - q y)]
  have hbound : q x ≤ (∫ t, q t ∂μ) + 2 * ∫ t, p t ∂μ := by
    have h := setIntegral_mono_on
      (integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞))
      (hqm.add (integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)))
      measurableSet_Icc hpoint
    change (∫ _ in Icc (0 : ℝ) 1, q x) ≤
      ∫ t in Icc (0 : ℝ) 1, q t + 2 * ∫ s, p s ∂μ at h
    rw [integral_add hqm (integrableOn_const (by simp)), setIntegral_const,
      setIntegral_const] at h
    simpa only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one, one_smul] using h
  exact hbound.trans (by
    change (∫ t, q t ∂μ) + 2 * ∫ t, p t ∂μ ≤ _
    nlinarith only [hholder])

private theorem norm_deriv_norm_le_ae_of_lipschitz
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ t ∂volume, ‖deriv (fun s => ‖f s‖) t‖ ≤ ‖deriv f t‖ := by
  have hr := lipschitzWith_one_norm.comp hf
  filter_upwards [hf.ae_differentiableAt_real, hr.ae_differentiableAt_real] with t ht hrt
  have h := DifferentialGeometry.Analysis.norm_differential_comp_le
    ht.hasFDerivAt hrt.hasFDerivAt lipschitzWith_one_norm (1 : ℝ)
  simpa only [fderiv_apply_one_eq_deriv, NNReal.coe_one, one_mul, Function.comp_def] using h

theorem norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖f x‖ ^ 2 ≤ (∫ t in Icc (0 : ℝ) 1, ‖f t‖ ^ 2) +
      2 * Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) := by
  have hr := lipschitzWith_one_norm.comp hf
  have hm := memLp_deriv_Icc_of_lipschitz hf
  have hrm := memLp_deriv_Icc_of_lipschitz hr
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hri := (memLp_two_iff_integrable_sq_norm hrm.aestronglyMeasurable).mp hrm
  have he : (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => ‖f s‖) t‖ ^ 2) ≤
      ∫ t in Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2 := by
    apply integral_mono_ae hri hi
    filter_upwards [ae_restrict_of_ae (norm_deriv_norm_le_ae_of_lipschitz hf)] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  have h := norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz_real hr hx
  simp only [Function.comp_def, norm_norm] at h
  apply h.trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz
    {a b : ℝ → F} {K L : ℝ≥0} (ha : LipschitzWith K a) (hb : LipschitzWith L b)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖a x - b x‖ ^ 2 ≤ (∫ t in Icc (0 : ℝ) 1, ‖a t - b t‖ ^ 2) +
      2 * Real.sqrt (∫ t in Icc (0 : ℝ) 1, ‖a t - b t‖ ^ 2) *
        Real.sqrt (2 * ∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2) := by
  have ham := memLp_deriv_Icc_of_lipschitz ha
  have hbm := memLp_deriv_Icc_of_lipschitz hb
  have habm := memLp_deriv_Icc_of_lipschitz (ha.sub hb)
  have hai := (memLp_two_iff_integrable_sq_norm ham.aestronglyMeasurable).mp ham
  have hbi := (memLp_two_iff_integrable_sq_norm hbm.aestronglyMeasurable).mp hbm
  have habi := (memLp_two_iff_integrable_sq_norm habm.aestronglyMeasurable).mp habm
  have he : (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun t => a t - b t) t‖ ^ 2) ≤
      2 * ∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae habi ((hai.add hbi).const_mul 2)
    filter_upwards [ae_restrict_of_ae ha.ae_differentiableAt_real,
      ae_restrict_of_ae hb.ae_differentiableAt_real] with t hat hbt
    change ‖deriv (fun t => a t - b t) t‖ ^ 2 ≤
      2 * (‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2)
    rw [deriv_fun_sub hat hbt]
    have hnorm := norm_sub_le (deriv a t) (deriv b t)
    nlinarith [norm_nonneg (deriv a t - deriv b t),
      norm_nonneg (deriv a t), norm_nonneg (deriv b t),
      sq_nonneg (‖deriv a t‖ - ‖deriv b t‖)]
  apply (norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz (ha.sub hb) hx).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem tendstoUniformlyOn_sub_zero_of_tendsto_integral_norm_sub_sq_of_deriv_bound
    (a b : ℕ → ℝ → F) (K L : ℕ → ℝ≥0)
    (ha : ∀ n, LipschitzWith (K n) (a n)) (hb : ∀ n, LipschitzWith (L n) (b n))
    {D : ℝ} (hD : ∀ n,
      (∫ t in Icc (0 : ℝ) 1, ‖deriv (a n) t‖ ^ 2 + ‖deriv (b n) t‖ ^ 2) ≤ D)
    (hlim : Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2)
      atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n t => a n t - b n t) (fun _ => 0) atTop (Icc (0 : ℝ) 1) := by
  let I (n : ℕ) := ∫ t in Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2
  let R (n : ℕ) := I n + 2 * Real.sqrt (I n) * Real.sqrt (2 * D)
  have hR : Tendsto R atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
    simpa only [R, I, Function.comp_def, Real.sqrt_zero, mul_zero, zero_mul, add_zero] using
      hlim.add ((hs.const_mul 2).mul_const (Real.sqrt (2 * D)))
  have hbnd (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ‖a n x - b n x‖ ^ 2 ≤ R n := by
    apply (norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz (ha n) (hb n) hx).trans
    dsimp only [R, I]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hD n) (by norm_num))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [((tendsto_order.1 hR).2 (ε ^ 2) (sq_pos_of_pos hε))] with n hn
  intro x hx
  have hs := (hbnd n x hx).trans_lt hn
  simpa only [dist_zero_left, norm_neg] using (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hs

end DifferentialGeometry.Analysis.Sobolev
