import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

def euclideanUnitBallVolume (n : ℕ) : ℝ :=
  Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)

def modelRadius (K t : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * t) / Real.sqrt K
  else if K = 0 then t
  else Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)

def modelRadiusDeriv (K t : ℝ) : ℝ :=
  if 0 < K then Real.cos (Real.sqrt K * t)
  else if K = 0 then 1
  else Real.cosh (Real.sqrt (-K) * t)


def modelDensity (K : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  modelRadius K t ^ d

def modelRadialVolume (K : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, modelDensity K d t


def modelDensityDeriv (K : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  (d : ℝ) * modelRadius K t ^ (d - 1) * modelRadiusDeriv K t


def modelMeanCurv (K : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  (d : ℝ) * modelRadiusDeriv K t / modelRadius K t

def modelArea (K : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * euclideanUnitBallVolume n * modelRadius K t ^ (n - 1)

def modelVolume (K : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, modelArea K n t

def modelRadiusAdmissible (K r : ℝ) : Prop :=
  0 < r ∧ (0 < K → r < Real.pi / Real.sqrt K)

def modelVolumeAdmissible (K r : ℝ) : Prop :=
  0 ≤ r ∧ (0 < K → r ≤ Real.pi / Real.sqrt K)


theorem euclideanUnitBallVolume_pos (n : ℕ) : 0 < euclideanUnitBallVolume n := by
  unfold euclideanUnitBallVolume
  positivity

theorem euclidean_volume_unitBall (n : ℕ) (hn : 1 ≤ n) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal =
      euclideanUnitBallVolume n := by
  let _ : Nonempty (Fin n) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  change (ENNReal.ofReal (euclideanUnitBallVolume n)).toReal = euclideanUnitBallVolume n
  rw [ENNReal.toReal_ofReal (euclideanUnitBallVolume_pos n).le]


@[simp] theorem modelRadius_zero (t : ℝ) : modelRadius 0 t = t := by
  simp [modelRadius]


@[simp] theorem modelRadius_at_zero (K : ℝ) : modelRadius K 0 = 0 := by
  by_cases hK : 0 < K
  · simp [modelRadius, hK]
  · by_cases hK0 : K = 0
    · simp [modelRadius, hK0]
    · simp [modelRadius, hK0]

theorem modelRadius_neg_sq (q t : ℝ) (hq : 0 ≤ q) :
    modelRadius (-(q ^ 2)) t = hyperbolicSn q t := by
  by_cases hq0 : q = 0
  · subst q
    simp [modelRadius, hyperbolicSn]
  · have hKpos : ¬0 < -(q ^ 2) :=
      not_lt.mpr (neg_nonpos.mpr (sq_nonneg q))
    have hK0 : -(q ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hq0)
    rw [modelRadius, if_neg hKpos, if_neg hK0, hyperbolicSn, if_neg hq0]
    rw [show Real.sqrt (-(-(q ^ 2))) = q by
      rw [neg_neg, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]]

theorem modelRadius_eq_hypSn_of_nonpos (K t : ℝ) (hK : K ≤ 0) :
    modelRadius K t = hyperbolicSn (Real.sqrt (-K)) t := by
  have hsqrt : Real.sqrt (-K) ^ 2 = -K := Real.sq_sqrt (neg_nonneg.mpr hK)
  rw [← modelRadius_neg_sq (Real.sqrt (-K)) t (Real.sqrt_nonneg (-K))]
  rw [hsqrt, neg_neg]


theorem hasDerivAt_modelRadius (K t : ℝ) :
    HasDerivAt (modelRadius K) (modelRadiusDeriv K t) t := by
  by_cases hK : 0 < K
  · have hq0 : Real.sqrt K ≠ 0 := (Real.sqrt_ne_zero').2 hK
    have h := (((hasDerivAt_id t).const_mul (Real.sqrt K)).sin.div_const (Real.sqrt K))
    rw [show modelRadius K = fun x => Real.sin (Real.sqrt K * x) / Real.sqrt K by
      funext x
      simp [modelRadius, hK]]
    simpa [modelRadiusDeriv, hK, hq0] using h
  · by_cases hK0 : K = 0
    · subst K
      rw [show modelRadius 0 = id by funext x; simp [modelRadius]]
      simpa [modelRadiusDeriv] using hasDerivAt_id t
    · have hneg : 0 < -K := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hK) hK0)
      have hq0 : Real.sqrt (-K) ≠ 0 := (Real.sqrt_ne_zero').2 hneg
      have h := (((hasDerivAt_id t).const_mul (Real.sqrt (-K))).sinh.div_const
        (Real.sqrt (-K)))
      rw [show modelRadius K = fun x => Real.sinh (Real.sqrt (-K) * x) / Real.sqrt (-K) by
        funext x
        simp [modelRadius, hK, hK0]]
      simpa [modelRadiusDeriv, hK, hK0, hq0] using h

theorem hasDerivAt_modelRadiusDeriv (K t : ℝ) :
    HasDerivAt (modelRadiusDeriv K) (-K * modelRadius K t) t := by
  by_cases hK : 0 < K
  · have hq0 : Real.sqrt K ≠ 0 := (Real.sqrt_ne_zero').2 hK
    have h := ((hasDerivAt_id t).const_mul (Real.sqrt K)).cos
    rw [show modelRadiusDeriv K = fun x => Real.cos (Real.sqrt K * x) by
      funext x
      simp [modelRadiusDeriv, hK]]
    convert h using 1
    · simp
    · rw [modelRadius, if_pos hK]
      field_simp
      rw [Real.sq_sqrt hK.le]
      simp
  · by_cases hK0 : K = 0
    · subst K
      rw [show modelRadiusDeriv 0 = fun _ => (1 : ℝ) by
        funext x
        simp [modelRadiusDeriv]]
      simpa [modelRadius] using (hasDerivAt_const (x := t) (c := (1 : ℝ)))
    · have hneg : 0 < -K := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hK) hK0)
      have hq0 : Real.sqrt (-K) ≠ 0 := (Real.sqrt_ne_zero').2 hneg
      have h := ((hasDerivAt_id t).const_mul (Real.sqrt (-K))).cosh
      rw [show modelRadiusDeriv K = fun x => Real.cosh (Real.sqrt (-K) * x) by
        funext x
        simp [modelRadiusDeriv, hK, hK0]]
      convert h using 1
      · simp
      · rw [modelRadius, if_neg hK, if_neg hK0]
        field_simp
        rw [Real.sq_sqrt hneg.le]
        simp


@[simp] theorem modelRadiusDeriv_at_zero (K : ℝ) : modelRadiusDeriv K 0 = 1 := by
  by_cases hK : 0 < K
  · simp [modelRadiusDeriv, hK]
  · by_cases hK0 : K = 0
    · simp [modelRadiusDeriv, hK0]
    · simp [modelRadiusDeriv, hK0]


theorem modelRadius_ode (K t : ℝ) :
    deriv (modelRadiusDeriv K) t + K * modelRadius K t = 0 := by
  rw [(hasDerivAt_modelRadiusDeriv K t).deriv]
  ring


theorem modelRadius_continuous (K : ℝ) : Continuous (modelRadius K) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_modelRadius K t).continuousAt


theorem modelRadiusDeriv_continuous (K : ℝ) : Continuous (modelRadiusDeriv K) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_modelRadiusDeriv K t).continuousAt


theorem modelRadius_energy (K t : ℝ) :
    modelRadiusDeriv K t ^ 2 + K * modelRadius K t ^ 2 = 1 := by
  by_cases hK : 0 < K
  · have hq0 : Real.sqrt K ≠ 0 := (Real.sqrt_ne_zero').2 hK
    rw [modelRadiusDeriv, if_pos hK, modelRadius, if_pos hK]
    have htrig := Real.cos_sq_add_sin_sq (Real.sqrt K * t)
    have hsqrt := Real.sq_sqrt hK.le
    field_simp
    nlinarith
  · by_cases hK0 : K = 0
    · subst K
      simp [modelRadiusDeriv, modelRadius]
    · have hneg : 0 < -K := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hK) hK0)
      have hq0 : Real.sqrt (-K) ≠ 0 := (Real.sqrt_ne_zero').2 hneg
      rw [modelRadiusDeriv, if_neg hK, if_neg hK0,
        modelRadius, if_neg hK, if_neg hK0]
      have hhyp := Real.cosh_sq_sub_sinh_sq (Real.sqrt (-K) * t)
      have hsqrt := Real.sq_sqrt hneg.le
      field_simp
      nlinarith

theorem modelRadius_pos {K t : ℝ} (ht : modelRadiusAdmissible K t) :
    0 < modelRadius K t := by
  rcases ht with ⟨ht, hupper⟩
  by_cases hK : 0 < K
  · have hqpos : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
    have hqtpos : 0 < Real.sqrt K * t := mul_pos hqpos ht
    have hqtlt : Real.sqrt K * t < Real.pi := by
      have h := (lt_div_iff₀ hqpos).mp (hupper hK)
      simpa [mul_comm] using h
    rw [modelRadius, if_pos hK]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hqtpos hqtlt) hqpos
  · by_cases hK0 : K = 0
    · simpa [modelRadius, hK0] using ht
    · have hneg : 0 < -K := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hK) hK0)
      have hqpos : 0 < Real.sqrt (-K) := Real.sqrt_pos.2 hneg
      rw [modelRadius, if_neg hK, if_neg hK0]
      exact div_pos (Real.sinh_pos_iff.2 (mul_pos hqpos ht)) hqpos

theorem modelRadius_nonneg {K t : ℝ} (ht : 0 ≤ t)
    (hadm : modelVolumeAdmissible K t) : 0 ≤ modelRadius K t := by
  by_cases hK : 0 < K
  · have hqpos : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
    have hqt0 : 0 ≤ Real.sqrt K * t := mul_nonneg hqpos.le ht
    have hqtpi : Real.sqrt K * t ≤ Real.pi := by
      have h := (le_div_iff₀ hqpos).mp (hadm.2 hK)
      simpa only [mul_comm] using h
    rw [modelRadius, if_pos hK]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hqt0 hqtpi) hqpos.le
  · by_cases hK0 : K = 0
    · simpa [modelRadius, hK0] using ht
    · have hneg : 0 < -K := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hK) hK0)
      have hqpos : 0 < Real.sqrt (-K) := Real.sqrt_pos.2 hneg
      rw [modelRadius, if_neg hK, if_neg hK0]
      exact div_nonneg
        (Real.sinh_nonneg_iff.2 (mul_nonneg hqpos.le ht)) hqpos.le


theorem eventually_modelRadiusAdmissible (K : ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), modelRadiusAdmissible K t := by
  by_cases hK : 0 < K
  · have hend : 0 < Real.pi / Real.sqrt K :=
      div_pos Real.pi_pos (Real.sqrt_pos.2 hK)
    have hIio : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < Real.pi / Real.sqrt K :=
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left) (Iio_mem_nhds hend)
    filter_upwards [self_mem_nhdsWithin, hIio] with t ht hupper
    exact ⟨ht, fun _ => hupper⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨ht, fun hK' => (hK hK').elim⟩


theorem modelRadiusRatio_tendsto (K : ℝ) :
    Tendsto (fun t => modelRadius K t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := (hasDerivAt_modelRadius K 0).tendsto_slope_zero_right
  convert h using 1
  · funext t
    simp [div_eq_inv_mul, smul_eq_mul]
  · simp


theorem modelLog_tendsto (K : ℝ) :
    Tendsto (fun t => modelRadiusDeriv K t / modelRadius K t)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hsn : Tendsto (modelRadius K) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hsn0 : Tendsto (modelRadius K) (𝓝 (0 : ℝ))
          (𝓝 (modelRadius K 0)) := (modelRadius_continuous K).continuousAt
      have hsn0' : Tendsto (modelRadius K) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using hsn0
      exact hsn0'.mono_left inf_le_left
    · filter_upwards [eventually_modelRadiusAdmissible K] with t ht
      exact modelRadius_pos ht
  have hsd : Tendsto (modelRadiusDeriv K) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hsd0 : Tendsto (modelRadiusDeriv K) (𝓝 (0 : ℝ))
        (𝓝 (modelRadiusDeriv K 0)) := (modelRadiusDeriv_continuous K).continuousAt
    have hsd0' : Tendsto (modelRadiusDeriv K) (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa using hsd0
    exact hsd0'.mono_left inf_le_left
  convert hsn.inv_tendsto_nhdsGT_zero.atTop_mul_pos zero_lt_one hsd using 1
  simp only [Pi.inv_apply, inv_mul_eq_div]


theorem hasDerivAt_modelDensity (K : ℝ) (d : ℕ) (t : ℝ) :
    HasDerivAt (modelDensity K d) (modelDensityDeriv K d t) t := by
  change HasDerivAt (modelRadius K ^ d)
    ((d : ℝ) * modelRadius K t ^ (d - 1) * modelRadiusDeriv K t) t
  exact (hasDerivAt_modelRadius K t).pow d


theorem modelDensity_pos {K t : ℝ} {d : ℕ} (ht : modelRadiusAdmissible K t) :
    0 < modelDensity K d t :=
  pow_pos (modelRadius_pos ht) d


theorem modelDensity_continuous (K : ℝ) (d : ℕ) :
    Continuous (modelDensity K d) := by
  exact (modelRadius_continuous K).pow d


theorem modelRadialVolume_continuous (K : ℝ) (d : ℕ) :
    Continuous (modelRadialVolume K d) := by
  change Continuous (fun r : ℝ => ∫ t in (0 : ℝ)..r, modelDensity K d t)
  exact intervalIntegral.continuous_primitive
    (fun a b => (modelDensity_continuous K d).intervalIntegrable a b) (0 : ℝ)

theorem modelRadialVolume_pos {K R : ℝ} (d : ℕ) (hR : 0 < R)
    (hadm : modelVolumeAdmissible K R) : 0 < modelRadialVolume K d R := by
  rw [modelRadialVolume]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((modelDensity_continuous K d).intervalIntegrable (0 : ℝ) R)
    (fun t ht => modelDensity_pos
      ⟨ht.1, fun hK => lt_of_lt_of_le ht.2 (hadm.2 hK)⟩) hR

theorem modelRadial_lintegral (K : ℝ) (d : ℕ) {R : ℝ} (hR : 0 < R)
    (hadm : modelVolumeAdmissible K R) :
    (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)),
        ENNReal.ofReal (modelDensity K d r.1 / r.1 ^ d)
        ∂Measure.volumeIoiPow d) =
      ENNReal.ofReal (modelRadialVolume K d R) := by
  have hpowMeas : Measurable (fun r : Set.Ioi (0 : ℝ) =>
      ENNReal.ofReal (r.1 ^ d)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const d)
  rw [Measure.volumeIoiPow]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    _ hpowMeas _ measurableSet_Iic]
  · have hmul :
      (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)),
          ENNReal.ofReal (r.1 ^ d) *
            ENNReal.ofReal (modelDensity K d r.1 / r.1 ^ d)
          ∂Measure.comap Subtype.val volume) =
        ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)),
          ENNReal.ofReal (modelDensity K d r.1)
          ∂Measure.comap Subtype.val volume := by
      apply setLIntegral_congr_fun measurableSet_Iic
      intro r _hr
      change ENNReal.ofReal (r.1 ^ d) *
          ENNReal.ofReal (modelDensity K d r.1 / r.1 ^ d) =
        ENNReal.ofReal (modelDensity K d r.1)
      rw [← ENNReal.ofReal_mul (pow_nonneg r.2.le d)]
      congr 1
      exact mul_div_cancel₀ (modelDensity K d r.1)
        (pow_ne_zero d r.2.ne')
    change
      (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)),
          ENNReal.ofReal (r.1 ^ d) *
            ENNReal.ofReal (modelDensity K d r.1 / r.1 ^ d)
          ∂Measure.comap Subtype.val volume) =
        ENNReal.ofReal (modelRadialVolume K d R)
    rw [hmul]
    rw [setLIntegral_subtype measurableSet_Ioi
      (Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)))
      (fun t : ℝ => ENNReal.ofReal (modelDensity K d t))]
    rw [Set.image_subtype_val_Ioi_Iic]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← intervalIntegral.integral_of_le hR.le]
      rfl
    · exact (modelDensity_continuous K d).continuousOn
        |>.intervalIntegrable_of_Icc hR.le |>.1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact pow_nonneg
        (modelRadius_nonneg ht.1.le
          ⟨ht.1.le, fun hK => ht.2.trans (hadm.2 hK)⟩) d
  · filter_upwards [] with r
    exact ENNReal.ofReal_lt_top


theorem modelDensityDeriv_eq_mean {K t : ℝ} {d : ℕ}
    (ht : modelRadiusAdmissible K t) :
    modelDensityDeriv K d t = modelMeanCurv K d t * modelDensity K d t := by
  have hs : modelRadius K t ≠ 0 := (modelRadius_pos ht).ne'
  cases d with
  | zero => simp [modelDensityDeriv, modelMeanCurv, modelDensity]
  | succ d =>
      simp only [modelDensityDeriv, modelMeanCurv, modelDensity, Nat.cast_succ,
        Nat.succ_sub_one, pow_succ]
      field_simp


theorem hasDerivAt_modelMeanCurv {K t : ℝ} {d : ℕ}
    (ht : modelRadiusAdmissible K t) (hd : 0 < d) :
    HasDerivAt (modelMeanCurv K d)
      (-((d : ℝ) * K) - modelMeanCurv K d t ^ 2 / (d : ℝ)) t := by
  have hs : modelRadius K t ≠ 0 := (modelRadius_pos ht).ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have h := ((hasDerivAt_modelRadiusDeriv K t).const_mul (d : ℝ)).fun_div
    (hasDerivAt_modelRadius K t) hs
  refine h.congr_deriv ?_
  have henergy := modelRadius_energy K t
  simp only [modelMeanCurv]
  field_simp


theorem hasDerivAt_modelLog {K t : ℝ} (ht : modelRadiusAdmissible K t) :
    HasDerivAt (fun x => modelRadiusDeriv K x / modelRadius K x)
      (-1 / modelRadius K t ^ 2) t := by
  have hs : modelRadius K t ≠ 0 := (modelRadius_pos ht).ne'
  have h := (hasDerivAt_modelRadiusDeriv K t).fun_div
    (hasDerivAt_modelRadius K t) hs
  refine h.congr_deriv ?_
  have henergy := modelRadius_energy K t
  field_simp [hs]
  nlinarith

theorem modelVolumeAdmissible_conjugateRadius {K : ℝ} (hK : 0 < K) :
    modelVolumeAdmissible K (Real.pi / Real.sqrt K) := by
  constructor
  · exact (div_pos Real.pi_pos (Real.sqrt_pos.2 hK)).le
  · intro
    exact le_rfl

theorem modelArea_neg_sq (q : ℝ) (n : ℕ) (t : ℝ) (hq : 0 ≤ q) :
    modelArea (-(q ^ 2)) n t =
      (n : ℝ) * euclideanUnitBallVolume n * hyperbolicDensity q (n - 1) t := by
  simp [modelArea, hyperbolicDensity, modelRadius_neg_sq q t hq]

theorem modelVolume_neg_sq (q : ℝ) (n : ℕ) (r : ℝ) (hq : 0 ≤ q) :
    modelVolume (-(q ^ 2)) n r =
      (n : ℝ) * euclideanUnitBallVolume n * hyperbolicRadialVolume q (n - 1) r := by
  rw [modelVolume, hyperbolicRadialVolume]
  simp_rw [modelArea, modelRadius_neg_sq q _ hq, hyperbolicDensity]
  rw [intervalIntegral.integral_const_mul]


theorem modelVolume_eq_hypRadVol_of_nonpos (K : ℝ) (n : ℕ) (r : ℝ)
    (hK : K ≤ 0) :
    modelVolume K n r =
      (n : ℝ) * euclideanUnitBallVolume n *
        hyperbolicRadialVolume (Real.sqrt (-K)) (n - 1) r := by
  have hsqrt : Real.sqrt (-K) ^ 2 = -K := Real.sq_sqrt (neg_nonneg.mpr hK)
  rw [← modelVolume_neg_sq (Real.sqrt (-K)) n r (Real.sqrt_nonneg (-K))]
  rw [hsqrt, neg_neg]

theorem modelVolume_zero (n : ℕ) (r : ℝ) (hn : 1 ≤ n) :
    modelVolume 0 n r = euclideanUnitBallVolume n * r ^ n := by
  have hbridge := modelVolume_neg_sq 0 n r (le_refl 0)
  norm_num only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero] at hbridge
  rw [hbridge, hyperbolicRadialVolume_zero, Nat.sub_add_cancel hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hn
  rw [hcast]
  field_simp


theorem euclideanSphereArea_eq (n : ℕ) (hn : 1 ≤ n) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ =
      ENNReal.ofReal ((n : ℝ) * euclideanUnitBallVolume n) := by
  let _ : Nonempty (Fin n) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [Measure.toSphere_apply_univ, EuclideanSpace.volume_ball]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_one, one_pow,
    one_mul]
  change (n : ℝ≥0∞) * ENNReal.ofReal (euclideanUnitBallVolume n) =
    ENNReal.ofReal ((n : ℝ) * euclideanUnitBallVolume n)
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  norm_num

theorem ofReal_modelVolume_neg_sq (q r : ℝ) (n : ℕ) (hn : 1 ≤ n) (hq : 0 ≤ q) :
    ENNReal.ofReal (modelVolume (-(q ^ 2)) n r) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ *
        ENNReal.ofReal (hyperbolicRadialVolume q (n - 1) r) := by
  rw [modelVolume_neg_sq q n r hq, euclideanSphereArea_eq n hn]
  rw [ENNReal.ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_pos n).le

theorem hyperbolicRadialVolume_scale (q c R : ℝ) (d : ℕ) (hc : 0 < c) :
    hyperbolicRadialVolume (q / c) d (c * R) = c ^ (d + 1) * hyperbolicRadialVolume q d R := by
  have hc0 : c ≠ 0 := hc.ne'
  have hqc : q / c * c = q := div_mul_cancel₀ q hc0
  calc
    hyperbolicRadialVolume (q / c) d (c * R) =
        c * ∫ t in (0 : ℝ)..R, hyperbolicDensity (q / c) d (c * t) := by
      rw [hyperbolicRadialVolume]
      symm
      simpa only [smul_eq_mul, mul_zero] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := hyperbolicDensity (q / c) d) (a := (0 : ℝ)) (b := R) c)
    _ = c * ∫ t in (0 : ℝ)..R, c ^ d * hyperbolicDensity q d t := by
      congr 2
      funext t
      rw [← hyperbolicDens_scale (q / c) c d t hc0, hqc]
    _ = c ^ (d + 1) * hyperbolicRadialVolume q d R := by
      rw [intervalIntegral.integral_const_mul, hyperbolicRadialVolume, pow_succ]
      ring


theorem modelVolume_neg_sq_scale (q c R : ℝ) (n : ℕ)
    (hq : 0 ≤ q) (hc : 0 < c) (hn : 1 ≤ n) :
    modelVolume (-((q / c) ^ 2)) n (c * R) =
      c ^ n * modelVolume (-(q ^ 2)) n R := by
  rw [modelVolume_neg_sq (q / c) n (c * R) (div_nonneg hq hc.le),
    modelVolume_neg_sq q n R hq, hyperbolicRadialVolume_scale q c R (n - 1) hc]
  rw [Nat.sub_add_cancel hn]
  ring


theorem modelArea_continuous (K : ℝ) (n : ℕ) : Continuous (modelArea K n) := by
  change Continuous (fun t : ℝ =>
    (n : ℝ) * euclideanUnitBallVolume n * modelRadius K t ^ (n - 1))
  exact (continuous_const.mul continuous_const).mul
    ((modelRadius_continuous K).pow (n - 1))

theorem modelVolume_eq_sphereFactor_mul_radialVolume
    (K : ℝ) (n : ℕ) (r : ℝ) :
    modelVolume K n r =
      ((n : ℝ) * euclideanUnitBallVolume n) *
        modelRadialVolume K (n - 1) r := by
  simp only [modelVolume, modelArea, modelRadialVolume, modelDensity,
    intervalIntegral.integral_const_mul]


theorem modelVolume_continuous (K : ℝ) (n : ℕ) : Continuous (modelVolume K n) := by
  change Continuous (fun r : ℝ => ∫ t in (0 : ℝ)..r, modelArea K n t)
  exact intervalIntegral.continuous_primitive
    (fun a b => (modelArea_continuous K n).intervalIntegrable a b) (0 : ℝ)


@[simp] theorem modelVolume_at_zero (K : ℝ) (n : ℕ) : modelVolume K n 0 = 0 := by
  simp [modelVolume]


theorem modelArea_pos {K t : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (ht : modelRadiusAdmissible K t) : 0 < modelArea K n t := by
  unfold modelArea
  exact mul_pos
    (mul_pos (Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hn))
      (euclideanUnitBallVolume_pos n))
    (pow_pos (modelRadius_pos ht) (n - 1))

theorem modelVolume_pos {K r : ℝ} {n : ℕ} (hn : 1 ≤ n) (hr : 0 < r)
    (hadm : modelVolumeAdmissible K r) : 0 < modelVolume K n r := by
  rw [modelVolume]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((modelArea_continuous K n).intervalIntegrable (0 : ℝ) r)
    (fun t ht => modelArea_pos hn ⟨ht.1, fun hK => lt_of_lt_of_le ht.2 (hadm.2 hK)⟩) hr

theorem euclideanUnitBallVolume_two : euclideanUnitBallVolume 2 = Real.pi := by
  rw [euclideanUnitBallVolume, Real.sq_sqrt Real.pi_pos.le]
  have harg : ((2 : ℕ) : ℝ) / 2 + 1 = ((1 : ℕ) : ℝ) + 1 := by norm_num
  rw [harg, Real.Gamma_nat_eq_factorial]
  norm_num

theorem modelVolume_one_two_pi : modelVolume 1 2 Real.pi = 4 * Real.pi := by
  rw [modelVolume_eq_sphereFactor_mul_radialVolume, euclideanUnitBallVolume_two]
  have hrad : modelRadialVolume 1 1 Real.pi = 2 := by
    rw [modelRadialVolume]
    have hdens : ∀ t : ℝ, modelDensity 1 1 t = Real.sin t := by
      intro t
      rw [modelDensity, pow_one, modelRadius, if_pos one_pos]
      norm_num
    simp_rw [hdens]
    rw [integral_sin, Real.cos_zero, Real.cos_pi]
    norm_num
  rw [hrad]
  ring

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
