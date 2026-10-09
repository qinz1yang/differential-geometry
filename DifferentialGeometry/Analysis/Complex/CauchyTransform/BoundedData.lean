import DifferentialGeometry.Analysis.Complex.CauchyTransform.Disk

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Bounded measurable disk data are integrable against the inverse kernel. -/
theorem integrable_diskCauchyIntegral_kernel {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ}
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B)
    (z : closedBall a R) :
    Integrable (fun w : closedBall a R => ((z : ℂ) - (w : ℂ))⁻¹ • f w)
      (volume.comap ((↑) : closedBall a R → ℂ)) := by
  have hi := (integrable_disk_inverse_kernel_and_bound hR z).1.mul_const B
  apply hi.mono'
  · exact ((measurable_const.sub measurable_subtype_coe).inv.aestronglyMeasurable).smul
      hf
  · filter_upwards [hbound] with w hw
    rw [norm_smul, norm_inv]
    exact mul_le_mul_of_nonneg_left hw (by positivity)

/-- The literal Cauchy integral of raw disk data, evaluated at an ambient point. -/
def diskCauchyIntegral {a : ℂ} {R : ℝ}
    (f : closedBall a R → F) (z : ℂ) : F :=
  (Real.pi : ℂ)⁻¹ • ∫ w : closedBall a R, (z - (w : ℂ))⁻¹ • f w
    ∂(volume.comap ((↑) : closedBall a R → ℂ))

/-- The raw bounded-data Cauchy integral has norm at most four times radius times bound. -/
theorem norm_diskCauchyIntegral_le {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B)
    (z : closedBall a R) :
    ‖diskCauchyIntegral f z‖ ≤ (4 * R) * B := by
  have hi := integrable_diskCauchyIntegral_kernel hR f hf hbound z
  obtain ⟨hk, hb⟩ := integrable_disk_inverse_kernel_and_bound hR z
  have hπ : ‖(Real.pi : ℂ)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ = Real.pi⁻¹ * ‖∫ w : closedBall a R, ((z : ℂ) - (w : ℂ))⁻¹ • f w
        ∂(volume.comap ((↑) : closedBall a R → ℂ))‖ := by
      rw [diskCauchyIntegral, norm_smul, hπ]
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R, ‖((z : ℂ) - (w : ℂ))⁻¹ • f w‖
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R, ‖(z : ℂ) - (w : ℂ)‖⁻¹ * B
        ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply integral_mono_ae hi.norm (hk.mul_const B)
      filter_upwards [hbound] with w hw
      rw [norm_smul, norm_inv]
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = Real.pi⁻¹ * ((∫ w : closedBall a R, ‖(z : ℂ) - (w : ℂ)‖⁻¹
        ∂(volume.comap ((↑) : closedBall a R → ℂ))) * B) := by
      rw [integral_mul_const]
    _ ≤ Real.pi⁻¹ * ((4 * Real.pi * R) * B) := by gcongr
    _ = _ := by field_simp

/-- The actual bounded-data integral satisfies a one-half Hölder estimate on the closed disk. -/
theorem norm_diskCauchyIntegral_sub_le {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B)
    (z z' : closedBall a R) :
    ‖diskCauchyIntegral f z - diskCauchyIntegral f z'‖ ≤
      16 * Real.sqrt R * B * Real.sqrt ‖(z : ℂ) - (z' : ℂ)‖ := by
  let μ : Measure (closedBall a R) := volume.comap ((↑) : closedBall a R → ℂ)
  let δ := ‖(z : ℂ) - (z' : ℂ)‖
  let b : ℝ := Real.sqrt (2 * δ) * B
  let k (z : closedBall a R) (w : closedBall a R) := ‖(z : ℂ) - (w : ℂ)‖ ^ (-(3 / 2 : ℝ))
  have hb : 0 ≤ b := by positivity
  obtain ⟨hk, hkb⟩ := integrable_disk_three_halves_kernel_and_bound hR z
  obtain ⟨hk', hkb'⟩ := integrable_disk_three_halves_kernel_and_bound hR z'
  have hmajor : Integrable (fun w => b * (k z w + k z' w)) μ :=
    (hk.add hk').const_mul b
  have hsing : ∀ᵐ w : closedBall a R ∂μ,
      (z : ℂ) - (w : ℂ) ≠ 0 ∧ (z' : ℂ) - (w : ℂ) ≠ 0 := by
    apply (ae_restrict_iff_subtype (μ := (volume : Measure ℂ)) (s := closedBall a R)
      (p := fun w : ℂ => (z : ℂ) - w ≠ 0 ∧ (z' : ℂ) - w ≠ 0)
      isClosed_closedBall.measurableSet).mp
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (z : ℂ)),
      ae_restrict_of_ae (volume.ae_ne (z' : ℂ))] with w hw hw'
    exact ⟨sub_ne_zero.mpr hw.symm, sub_ne_zero.mpr hw'.symm⟩
  have hpoint : ∀ᵐ w : closedBall a R ∂μ,
      ‖((z : ℂ) - (w : ℂ))⁻¹ • f w - ((z' : ℂ) - (w : ℂ))⁻¹ • f w‖ ≤
        b * (k z w + k z' w) := by
    filter_upwards [hsing, hbound] with w hw hfw
    rw [← sub_smul, norm_smul]
    have hh := norm_inv_sub_le_sqrt hw.1 hw.2
    rw [sub_sub_sub_cancel_right] at hh
    calc
      _ ≤ (Real.sqrt (2 * δ) * (k z w + k z' w)) * B :=
        mul_le_mul hh hfw (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [b]; ring
  have hi := (integrable_diskCauchyIntegral_kernel hR f hf hbound z).sub
    (integrable_diskCauchyIntegral_kernel hR f hf hbound z')
  have hπ : ‖(Real.pi : ℂ)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ = Real.pi⁻¹ * ‖∫ w : closedBall a R,
        (((z : ℂ) - (w : ℂ))⁻¹ • f w - ((z' : ℂ) - (w : ℂ))⁻¹ • f w) ∂μ‖ := by
      rw [diskCauchyIntegral, diskCauchyIntegral, ← smul_sub,
        ← integral_sub (integrable_diskCauchyIntegral_kernel hR f hf hbound z)
          (integrable_diskCauchyIntegral_kernel hR f hf hbound z'), norm_smul, hπ]
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R,
        ‖((z : ℂ) - (w : ℂ))⁻¹ • f w - ((z' : ℂ) - (w : ℂ))⁻¹ • f w‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ Real.pi⁻¹ * ∫ w : closedBall a R, b * (k z w + k z' w) ∂μ :=
      mul_le_mul_of_nonneg_left (integral_mono_ae hi.norm hmajor hpoint) (by positivity)
    _ = Real.pi⁻¹ * (b * ((∫ w, k z w ∂μ) + ∫ w, k z' w ∂μ)) := by
      rw [integral_const_mul, integral_add hk hk']
    _ ≤ Real.pi⁻¹ * (b * (8 * Real.pi * Real.sqrt (2 * R))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hb
      linarith
    _ = _ := by
      dsimp [b, δ]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ = (8 * (Real.sqrt 2) ^ 2) * Real.sqrt R * B *
            Real.sqrt ‖(z : ℂ) - (z' : ℂ)‖ := by field_simp
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

/-- The actual integral representative of bounded measurable disk data is continuous. -/
theorem continuous_diskCauchyIntegral {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B) :
    Continuous (fun z : closedBall a R => diskCauchyIntegral f z) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun w => norm_nonneg _)
    (fun w => norm_diskCauchyIntegral_sub_le hR f hf hB hbound w z)
  have hc : Continuous (fun w : closedBall a R =>
      16 * Real.sqrt R * B * Real.sqrt ‖(w : ℂ) - (z : ℂ)‖) :=
    continuous_const.mul (Real.continuous_sqrt.comp
      ((continuous_subtype_val.sub continuous_const).norm))
  simpa using hc.tendsto z

/-- The continuous representative of the literal Cauchy integral of bounded measurable data. -/
def boundedDiskCauchyTransform {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B) :
    C(closedBall a R, F) :=
  ⟨fun z => diskCauchyIntegral f z, continuous_diskCauchyIntegral hR f hf hB hbound⟩

/-- The bundled continuous representative is the same literal integral at every disk point. -/
@[simp] theorem boundedDiskCauchyTransform_apply {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B)
    (z : closedBall a R) :
    boundedDiskCauchyTransform hR f hf hB hbound z = diskCauchyIntegral f z := rfl

/-- The continuous representative has sup norm at most four times radius times bound. -/
theorem norm_boundedDiskCauchyTransform_le {a : ℂ} {R : ℝ} (hR : 0 < R)
    (f : closedBall a R → F)
    (hf : AEStronglyMeasurable f (volume.comap ((↑) : closedBall a R → ℂ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ w : closedBall a R ∂(volume.comap ((↑) : closedBall a R → ℂ)), ‖f w‖ ≤ B) :
    ‖boundedDiskCauchyTransform hR f hf hB hbound‖ ≤ 4 * R * B := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  exact norm_diskCauchyIntegral_le hR f hf hB hbound

end DifferentialGeometry.Analysis
