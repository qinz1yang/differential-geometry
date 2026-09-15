import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.MixedNorm

noncomputable section

open MeasureTheory Filter

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {T : ℝ}

theorem memLp_mul_norm_add_const (f : timeL2 X T) (K D : ℝ) :
    MemLp (fun t => K * ‖f t‖ + D) 2 (timeMeasure T) := by
  convert ((Lp.memLp f).norm.const_smul K).add (memLp_const D) using 1
  ext t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

def affineNormMajorant (f : timeL2 X T) (K D : ℝ) : timeL2 ℝ T :=
  (memLp_mul_norm_add_const f K D).toLp (fun t => K * ‖f t‖ + D)

theorem affineNormMajorant_ae (f : timeL2 X T) (K D : ℝ) :
    affineNormMajorant f K D =ᵐ[timeMeasure T] fun t => K * ‖f t‖ + D :=
  (memLp_mul_norm_add_const f K D).coeFn_toLp

theorem timeL2_norm_le_of_ae_affine_bound (g : timeL2 Y T) (f : timeL2 X T)
    {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖g t‖ ≤ K * ‖f t‖ + D) :
    ‖g‖ ≤ K * ‖f‖ + Real.sqrt T * D := by
  have h := timeL2_norm_le_of_ae_mixed_bound g f (const T D) hK (by norm_num : (0 : ℝ) ≤ 1) ?_
  · simpa only [norm_const, Real.norm_eq_abs, abs_of_nonneg hD, one_mul] using h
  · filter_upwards [hbound, coeFn_const (T := T) D] with t ht hc
    simpa only [hc, Real.norm_eq_abs, abs_of_nonneg hD, one_mul] using ht

theorem affineNormMajorant_norm_le (f : timeL2 X T) {K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) :
    ‖affineNormMajorant f K D‖ ≤ K * ‖f‖ + Real.sqrt T * D := by
  apply timeL2_norm_le_of_ae_affine_bound _ f hK hD
  filter_upwards [affineNormMajorant_ae f K D] with t ht
  rw [ht, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem memLp_of_ae_norm_le_mul_norm_add_const (f : timeL2 X T) {g : ℝ → Y}
    (hg : AEStronglyMeasurable g (timeMeasure T)) {K D : ℝ}
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖g t‖ ≤ K * ‖f t‖ + D) :
    MemLp g 2 (timeMeasure T) :=
  (memLp_mul_norm_add_const f K D).mono' hg hbound

theorem norm_toLp_le_of_ae_norm_le_mul_norm_add_const (f : timeL2 X T) {g : ℝ → Y}
    (hg : AEStronglyMeasurable g (timeMeasure T)) {K D : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖g t‖ ≤ K * ‖f t‖ + D) :
    ‖(memLp_of_ae_norm_le_mul_norm_add_const f hg hbound).toLp g‖ ≤
      K * ‖f‖ + Real.sqrt T * D := by
  apply timeL2_norm_le_of_ae_affine_bound _ f hK hD
  filter_upwards [(memLp_of_ae_norm_le_mul_norm_add_const f hg hbound).coeFn_toLp,
    hbound] with t ht hb
  simpa only [ht] using hb

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
