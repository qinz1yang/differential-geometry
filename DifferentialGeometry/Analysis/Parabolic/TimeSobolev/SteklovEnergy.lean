import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Steklov
noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem timeL2.tendsto_integral_bilinear_steklovAverage
    {T : ℝ} (A : ℝ → X →L[ℝ] Y →L[ℝ] Z)
    (hA : ∀ x y, AEStronglyMeasurable (fun t => A t x y) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C)
    (u : timeL2 X T) (v : timeL2 Y T) :
    Tendsto (fun h => ∫ t, A t (u t)
        (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage h
          ((Icc (0 : ℝ) T).indicator v) t) ∂timeMeasure T)
      (𝓝[≠] 0) (𝓝 (∫ t, A t (u t) (v t) ∂timeMeasure T)) := by
  have h := ((MeasureTheory.continuous_integral_bilinear_lp_right A hA hC u).tendsto v).comp
    (v.tendsto_steklovAverage)
  apply h.congr'
  filter_upwards [] with h
  apply integral_congr_ae
  filter_upwards [timeL2.coeFn_steklovAverage h v] with t ht
  rw [ht]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
private theorem integral_timeL2_indicator_bilinear_diag
    {T : ℝ} (B : X →L[ℝ] X →L[ℝ] ℝ) (u : timeL2 X T) :
    (∫ t, B (u t) (u t) ∂timeMeasure T) =
      ∫ t, B ((Icc (0 : ℝ) T).indicator u t)
        ((Icc (0 : ℝ) T).indicator u t) := by
  unfold timeMeasure
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht, map_zero]

omit [CompleteSpace X] in
private theorem integral_timeL2_indicator_weight_diffQuot
    {T : ℝ} (B : X →L[ℝ] X →L[ℝ] ℝ) (ζ : ℝ → ℝ) (u : timeL2 X T) (s : ℝ) :
    (∫ t, ζ t * B (u t) (s⁻¹ • ((Icc (0 : ℝ) T).indicator u (t + s) -
      (Icc (0 : ℝ) T).indicator u t)) ∂timeMeasure T) =
      ∫ t, ζ t * B ((Icc (0 : ℝ) T).indicator u t)
        (s⁻¹ • ((Icc (0 : ℝ) T).indicator u (t + s) -
          (Icc (0 : ℝ) T).indicator u t)) := by
  unfold timeMeasure
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht, map_zero, zero_apply, mul_zero]

theorem timeL2.integral_bilinear_le_of_cutoff_steklov_identity
    {T : ℝ} (A D : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ x y, AEStronglyMeasurable (fun t => A t x y) (timeMeasure T))
    (hD : ∀ x y, AEStronglyMeasurable (fun t => D t x y) (timeMeasure T))
    {CA CD : ℝ} (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ CA)
    (hCD : ∀ᵐ t ∂timeMeasure T, ‖D t‖ ≤ CD)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : timeL2 X T)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ)
    (htest : ∀ s : ℝ, 0 < s →
      (∫ t, A t (u t) (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
          ((Icc (0 : ℝ) T).indicator u) t)
        ∂timeMeasure T) =
        (∫ t, D t (u t) (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
          ((Icc (0 : ℝ) T).indicator u) t)
          ∂timeMeasure T) +
          ∫ t, ζ t * B (u t)
            (s⁻¹ • ((Icc (0 : ℝ) T).indicator u (t + s) -
              (Icc (0 : ℝ) T).indicator u t)) ∂timeMeasure T) :
    (∫ t, A t (u t) (u t) ∂timeMeasure T) ≤
      (∫ t, D t (u t) (u t) ∂timeMeasure T) + ((K : ℝ) / 2) *
        ∫ t, B (u t) (u t) ∂timeMeasure T := by
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun _ h => ne_of_gt h)
  have hleft := (timeL2.tendsto_integral_bilinear_steklovAverage A hA hCA u u).mono_left hfilter
  have hright := ((timeL2.tendsto_integral_bilinear_steklovAverage D hD hCD u u).mono_left hfilter).add_const
    (((K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [htest s hs]
  have hU : MemLp ((Icc (0 : ℝ) T).indicator u) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc).mpr (Lp.memLp u)
  have hζ' : MemLp ζ ∞ volume := hζ
  have henergy := integral_mul_bilinear_diffQuot_le B hB hBpos hU hζ' hζpos hζlip
    hs
  rw [← integral_timeL2_indicator_bilinear_diag B u,
    ← integral_timeL2_indicator_weight_diffQuot B ζ u s] at henergy
  exact add_le_add_right henergy _

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem timeL2.integral_mul_bilinear_le_of_forced_cutoff_steklov_identity
    {T : ℝ} (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : timeL2 X T) (ℓ : timeL2 (X →L[ℝ] ℝ) T)
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ)
    (htest : ∀ s : ℝ, 0 < s →
      (∫ t, ζ t * F t (u t)
          (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
            ((Icc (0 : ℝ) T).indicator u) t) ∂timeMeasure T) =
        (∫ t, _root_.deriv ζ t * B (u t)
          (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
            ((Icc (0 : ℝ) T).indicator u) t) ∂timeMeasure T) +
          (∫ t, ζ t * B (u t)
            (s⁻¹ • ((Icc (0 : ℝ) T).indicator u (t + s) -
              (Icc (0 : ℝ) T).indicator u t)) ∂timeMeasure T) +
          ∫ t, ζ t * ℓ t
            (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
              ((Icc (0 : ℝ) T).indicator u) t) ∂timeMeasure T) :
    (∫ t, ζ t * F t (u t) (u t) ∂timeMeasure T) ≤
      (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T +
        ∫ t, ζ t * ℓ t (u t) ∂timeMeasure T := by
  let A : ℝ → X →L[ℝ] X →L[ℝ] ℝ := fun t => ζ t • F t
  let D : ℝ → X →L[ℝ] X →L[ℝ] ℝ := fun t => _root_.deriv ζ t • B
  let P : ℝ → (X →L[ℝ] ℝ) →L[ℝ] X →L[ℝ] ℝ := fun t =>
    ζ t • ContinuousLinearMap.id ℝ (X →L[ℝ] ℝ)
  have hA : ∀ x y, AEStronglyMeasurable (fun t => A t x y) (timeMeasure T) := by
    intro x y
    exact (hζsmooth.continuous.aestronglyMeasurable.mul (hF x y)).congr
      (Eventually.of_forall fun t => by simp only [A, smul_apply, smul_eq_mul, Pi.mul_apply])
  have hD : ∀ x y, AEStronglyMeasurable (fun t => D t x y) (timeMeasure T) := by
    intro x y
    simpa only [D, smul_apply, smul_eq_mul] using
      (hζsmooth.continuous_deriv_one.aestronglyMeasurable (μ := timeMeasure T)).mul_const (B x y)
  have hP : ∀ x y, AEStronglyMeasurable (fun t => P t x y) (timeMeasure T) := by
    intro x y
    simpa only [P, smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply] using
      (hζsmooth.continuous.aestronglyMeasurable (μ := timeMeasure T)).mul_const (x y)
  obtain ⟨L, hL⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (show eLpNormEssSup ζ volume < ∞ by simpa only [eLpNorm_exponent_top] using hζ.eLpNorm_lt_top)
  have hAbound : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (L : ℝ) * max CF 0 := by
    filter_upwards [hCF, ae_restrict_of_ae hL] with t hFt hLt
    dsimp only [A]
    rw [norm_smul]
    have hLt' : ‖ζ t‖ ≤ (L : ℝ) := by exact_mod_cast hLt
    exact mul_le_mul hLt' (hFt.trans (le_max_left _ _)) (norm_nonneg _) L.coe_nonneg
  have hDbound : ∀ᵐ t ∂timeMeasure T, ‖D t‖ ≤ (K : ℝ) * ‖B‖ := by
    filter_upwards [] with t
    dsimp only [D]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hζlip) (norm_nonneg B)
  have hPbound : ∀ᵐ t ∂timeMeasure T,
      ‖P t‖ ≤ (L : ℝ) * ‖ContinuousLinearMap.id ℝ (X →L[ℝ] ℝ)‖ := by
    filter_upwards [ae_restrict_of_ae hL] with t hLt
    dsimp only [P]
    rw [norm_smul]
    have hLt' : ‖ζ t‖ ≤ (L : ℝ) := by exact_mod_cast hLt
    exact mul_le_mul_of_nonneg_right hLt' (norm_nonneg _)
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun _ h => ne_of_gt h)
  have hleft := (timeL2.tendsto_integral_bilinear_steklovAverage A hA hAbound u u).mono_left hfilter
  have hright := (((timeL2.tendsto_integral_bilinear_steklovAverage D hD hDbound u u).mono_left hfilter).add_const
    (((K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T)).add
      ((timeL2.tendsto_integral_bilinear_steklovAverage P hP hPbound ℓ u).mono_left hfilter)
  have hmain : (∫ t, A t (u t) (u t) ∂timeMeasure T) ≤
      (∫ t, D t (u t) (u t) ∂timeMeasure T) +
        ((K : ℝ) / 2) * (∫ t, B (u t) (u t) ∂timeMeasure T) +
        ∫ t, P t (ℓ t) (u t) ∂timeMeasure T := by
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [self_mem_nhdsWithin] with s hs
    change (∫ t, ζ t * F t (u t)
      (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
        ((Icc (0 : ℝ) T).indicator u) t) ∂timeMeasure T) ≤ _
    rw [htest s hs]
    have hU : MemLp ((Icc (0 : ℝ) T).indicator u) 2 volume :=
      (memLp_indicator_iff_restrict measurableSet_Icc).mpr (Lp.memLp u)
    have henergy := integral_mul_bilinear_diffQuot_le B hB hBpos hU hζ hζpos hζlip hs
    rw [← integral_timeL2_indicator_bilinear_diag B u,
      ← integral_timeL2_indicator_weight_diffQuot B ζ u s] at henergy
    exact add_le_add_left (add_le_add_right henergy _) _
  have hint : Integrable (fun t => B (u t) (u t)) (timeMeasure T) :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      (Lp.memLp u) (Lp.memLp u)
  have hβLp : MemLp (_root_.deriv ζ) ∞ (timeMeasure T) :=
    memLp_top_of_bound hζsmooth.continuous_deriv_one.aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hζlip)
  have hβbound : (∫ t, D t (u t) (u t) ∂timeMeasure T) ≤
      (K : ℝ) * ∫ t, B (u t) (u t) ∂timeMeasure T := by
    rw [← integral_const_mul]
    have hmul := hint.mul_of_top_right hβLp
    have hintD : Integrable (fun t => D t (u t) (u t)) (timeMeasure T) := by
      exact hmul.congr (Eventually.of_forall fun t => by
        simp only [D, smul_apply, smul_eq_mul, Pi.mul_apply])
    apply integral_mono_ae hintD (hint.const_mul _)
    filter_upwards [] with t
    change _root_.deriv ζ t * B (u t) (u t) ≤ _
    exact mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (norm_deriv_le_of_lipschitz hζlip)) (hBpos _)
  change (∫ t, A t (u t) (u t) ∂timeMeasure T) ≤
    (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T +
      ∫ t, P t (ℓ t) (u t) ∂timeMeasure T
  linarith

theorem timeL2.integral_mul_bilinear_le_of_cutoff_steklov_identity
    {T : ℝ} (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : timeL2 X T)
    {ζ : ℝ → ℝ} (hζsmooth : ContDiff ℝ 1 ζ)
    (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ)
    (htest : ∀ s : ℝ, 0 < s →
      (∫ t, ζ t * F t (u t)
          (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
            ((Icc (0 : ℝ) T).indicator u) t) ∂timeMeasure T) =
        (∫ t, _root_.deriv ζ t * B (u t)
          (DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage s
            ((Icc (0 : ℝ) T).indicator u) t) ∂timeMeasure T) +
          ∫ t, ζ t * B (u t)
            (s⁻¹ • ((Icc (0 : ℝ) T).indicator u (t + s) -
              (Icc (0 : ℝ) T).indicator u t)) ∂timeMeasure T) :
    (∫ t, ζ t * F t (u t) (u t) ∂timeMeasure T) ≤
      (3 * (K : ℝ) / 2) * ∫ t, B (u t) (u t) ∂timeMeasure T := by
  have hzero (v : ℝ → X) : (∫ t, ζ t * (0 : timeL2 (X →L[ℝ] ℝ) T) t (v t)
      ∂timeMeasure T) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero (X →L[ℝ] ℝ) 2 (timeMeasure T)] with t ht
    rw [ht]
    simp only [Pi.zero_apply, zero_apply, mul_zero]
  have h := u.integral_mul_bilinear_le_of_forced_cutoff_steklov_identity F hF hCF B hB hBpos
    0 hζsmooth hζ hζpos hζlip (fun s hs => by simpa only [hzero, add_zero] using htest s hs)
  simpa only [hzero, add_zero] using h

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
