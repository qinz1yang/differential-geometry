import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.MixedNorm

noncomputable section

open MeasureTheory Filter

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {T : ℝ}

theorem memLp_mul_norm_add_const (f : timeL2 X T) (K D : ℝ) :
    MemLp (fun t => K * ‖f t‖ + D) 2 (timeMeasure T) := by
  exact ((Lp.memLp f).norm.const_smul K).add (memLp_const D)

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

section

open Set

variable [NormedSpace ℝ X] [NormedSpace ℝ Y]

theorem exists_timeL2_affine_comp_norm_le (H : ℝ × X →L[ℝ] Y) (f₀ : X)
    (T : ℝ) (hT : T ≤ 1) (u : timeL2 X T) :
    ∃ v : timeL2 Y T,
      v =ᵐ[timeMeasure T] (fun t => H (t, f₀ + u t)) ∧
      ‖v‖ ≤ (‖H‖ * (2 + ‖f₀‖)) * (Real.sqrt T + ‖u‖) := by
  have ht : MemLp (fun t : ℝ => (t, (0 : X))) 2 (timeMeasure T) :=
    memLp_of_continuousOn (continuousOn_id.prodMk continuousOn_const)
  have hu : MemLp (fun t => f₀ + u t) 2 (timeMeasure T) :=
    (memLp_const f₀).add (Lp.memLp u)
  have hp : MemLp (fun t => (t, f₀ + u t)) 2 (timeMeasure T) := by
    have hh := ht.add ((ContinuousLinearMap.inr ℝ ℝ X).comp_memLp' hu)
    apply hh.ae_eq
    filter_upwards [] with t
    simp only [Function.comp_apply, Pi.add_apply, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  have hv : MemLp (fun t => H (t, f₀ + u t)) 2 (timeMeasure T) :=
    H.comp_memLp' hp
  let v := hv.toLp (fun t => H (t, f₀ + u t))
  let B := ‖H‖ * (2 + ‖f₀‖)
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) (by positivity)
  refine ⟨v, hv.coeFn_toLp, ?_⟩
  have hpoint : ∀ᵐ t ∂timeMeasure T, ‖v t‖ ≤ B * ‖u t‖ + B := by
    filter_upwards [hv.coeFn_toLp, ae_restrict_mem measurableSet_Icc] with t ht htt
    change v t = H (t, f₀ + u t) at ht
    rw [ht]
    have hp : ‖(t, f₀ + u t)‖ ≤ 1 + ‖f₀‖ + ‖u t‖ := by
      rw [Prod.norm_def]
      apply max_le
      · rw [Real.norm_eq_abs, abs_of_nonneg htt.1]
        exact (htt.2.trans hT).trans (by linarith [norm_nonneg f₀, norm_nonneg (u t)])
      · exact (norm_add_le _ _).trans (by linarith)
    calc
      ‖H (t, f₀ + u t)‖ ≤ ‖H‖ * ‖(t, f₀ + u t)‖ := H.le_opNorm _
      _ ≤ ‖H‖ * (1 + ‖f₀‖ + ‖u t‖) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ B * ‖u t‖ + B := by
        dsimp only [B]
        nlinarith [norm_nonneg H, norm_nonneg f₀, norm_nonneg (u t),
          mul_nonneg (norm_nonneg H) (mul_nonneg (norm_nonneg f₀) (norm_nonneg (u t)))]
  calc
    ‖v‖ ≤ B * ‖u‖ + Real.sqrt T * B :=
      timeL2_norm_le_of_ae_affine_bound v u hB hB hpoint
    _ = (‖H‖ * (2 + ‖f₀‖)) * (Real.sqrt T + ‖u‖) := by dsimp only [B]; ring

end

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
