import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def steklovAverage (h : ℝ) (f : ℝ → X) (t : ℝ) : X :=
  h⁻¹ • ∫ s in t..t + h, f s

theorem steklovAverage_congr_ae
    {f g : ℝ → X} (hfg : f =ᵐ[volume] g) (h t : ℝ) :
    steklovAverage h f t = steklovAverage h g t := by
  unfold steklovAverage
  congr 1
  exact intervalIntegral.integral_congr_ae (hfg.mono fun _ hx _ => hx)

theorem steklovAverage_comp_continuousLinearMap {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (L : X →L[ℝ] Y) {f : ℝ → X} {h t : ℝ}
    (hf : IntervalIntegrable f volume t (t + h)) :
    steklovAverage h (fun s => L (f s)) t = L (steklovAverage h f t) := by
  simp only [steklovAverage, map_smul, L.intervalIntegral_comp_comm hf]

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace MeasureTheory.Lp

variable {X : Type*} [NormedAddCommGroup X]

def translate (r : ℝ) (u : Lp X 2 (volume : Measure ℝ)) : Lp X 2 (volume : Measure ℝ) :=
  compMeasurePreserving (fun t => t + r) (measurePreserving_add_right volume r) u

theorem coeFn_translate (r : ℝ) (u : Lp X 2 (volume : Measure ℝ)) :
    translate r u =ᵐ[volume] (fun t => u (t + r)) :=
  coeFn_compMeasurePreserving u (measurePreserving_add_right volume r)

@[simp] theorem norm_translate (r : ℝ) (u : Lp X 2 (volume : Measure ℝ)) :
    ‖translate r u‖ = ‖u‖ := norm_compMeasurePreserving u _

@[simp] theorem translate_zero (u : Lp X 2 (volume : Measure ℝ)) : translate 0 u = u := by
  simp only [translate, add_zero]
  exact compMeasurePreserving_id_apply u

theorem continuous_translate (u : Lp X 2 (volume : Measure ℝ)) : Continuous (fun r : ℝ => translate r u) := by
  let g : C(ℝ, C(ℝ, ℝ)) := (ContinuousMap.mk (fun p : ℝ × ℝ => p.2 + p.1)
    (continuous_snd.add continuous_fst)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous
    (fun r => measurePreserving_add_right volume r) (by norm_num)

variable [NormedSpace ℝ X]

def steklovAverage (h : ℝ) (u : Lp X 2 (volume : Measure ℝ)) : Lp X 2 (volume : Measure ℝ) :=
  h⁻¹ • ∫ r in (0 : ℝ)..h, translate r u

theorem norm_steklovAverage_le (h : ℝ) (u : Lp X 2 (volume : Measure ℝ)) :
    ‖steklovAverage h u‖ ≤ ‖u‖ := by
  by_cases hh : h = 0
  · simp [steklovAverage, hh]
  have hhabs : |h| ≠ 0 := abs_ne_zero.mpr hh
  calc
    ‖steklovAverage h u‖ = |h|⁻¹ * ‖∫ r in (0 : ℝ)..h, translate r u‖ := by
      rw [steklovAverage, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |h|⁻¹ * (‖u‖ * |h|) := by
      gcongr
      simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
        (fun r _ => (norm_translate r u).le)
    _ = ‖u‖ := by field_simp

variable [CompleteSpace X]

theorem tendsto_steklovAverage (u : Lp X 2 (volume : Measure ℝ)) :
    Tendsto (fun h => steklovAverage h u) (𝓝[≠] 0) (𝓝 u) := by
  have hc := continuous_translate u
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [translate_zero, steklovAverage, zero_add, intervalIntegral.integral_same,
    sub_zero] using hd.tendsto_slope_zero

end MeasureTheory.Lp

namespace MeasureTheory.Lp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

private def setIntegralContinuousLinearMap (S : Set ℝ) (hS : MeasurableSet S)
    (hvol : volume S ≠ ∞) : Lp X 2 (volume : Measure ℝ) →L[ℝ] X :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume 2 2 (indicatorConstLp 2 hS hvol (1 : ℝ))

private theorem setIntegralContinuousLinearMap_apply (S : Set ℝ) (hS : MeasurableSet S)
    (hvol : volume S ≠ ∞) (u : Lp X 2 (volume : Measure ℝ)) :
    setIntegralContinuousLinearMap S hS hvol u = ∫ t in S, u t := by
  rw [setIntegralContinuousLinearMap, ContinuousLinearMap.lpPairing_eq_integral]
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hvol) (c := (1 : ℝ))] with t ht
  rw [ContinuousLinearMap.lsmul_apply, ht]
  by_cases htS : t ∈ S
  · simp only [indicator_of_mem htS, one_smul]
  · simp only [indicator_of_notMem htS, zero_smul]

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem setIntegral_norm_le_mul_norm (S : Set ℝ) (hS : MeasurableSet S)
    (hvol : volume S ≠ ∞) (u : Lp X 2 (volume : Measure ℝ)) :
    (∫ t in S, ‖u t‖) ≤ ‖setIntegralContinuousLinearMap (X := ℝ) S hS hvol‖ * ‖u‖ := by
  let v : Lp ℝ 2 (volume : Measure ℝ) := (Lp.memLp u).norm.toLp (fun t => ‖u t‖)
  have hnorm : ‖v‖ = ‖u‖ := by
    rw [show v = (Lp.memLp u).norm.toLp (fun t => ‖u t‖) from rfl, Lp.norm_toLp, eLpNorm_norm]
    rfl
  have heq : (∫ t in S, ‖u t‖) = setIntegralContinuousLinearMap S hS hvol v := by
    rw [setIntegralContinuousLinearMap_apply]
    exact integral_congr_ae (ae_restrict_of_ae (MemLp.coeFn_toLp (Lp.memLp u).norm).symm)
  rw [heq]
  calc
    _ ≤ ‖setIntegralContinuousLinearMap S hS hvol v‖ := le_abs_self _
    _ ≤ ‖setIntegralContinuousLinearMap S hS hvol‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hnorm]

omit [NormedSpace ℝ X] [CompleteSpace X] in
private theorem integrable_translate_prod (u : Lp X 2 (volume : Measure ℝ))
    (a b : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hvol : volume S < ∞) :
    Integrable (fun q : ℝ × ℝ => u (q.2 + q.1))
      ((volume.restrict (Ioc a b)).prod (volume.restrict S)) := by
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hvol⟩
  have hmeas : StronglyMeasurable (fun q : ℝ × ℝ => u (q.2 + q.1)) :=
    (Lp.stronglyMeasurable u).comp_measurable (measurable_snd.add measurable_fst)
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun r =>
      (((Lp.memLp u).comp_measurePreserving (measurePreserving_add_right volume r)).restrict S).integrable (by norm_num)
  · apply Integrable.mono' (integrable_const (‖setIntegralContinuousLinearMap (X := ℝ) S hS hvol.ne‖ * ‖u‖))
      hmeas.norm.aestronglyMeasurable.integral_prod_right'
    refine Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg (u (t + r)))]
    have heq : (∫ t in S, ‖u (t + r)‖) = ∫ t in S, ‖translate r u t‖ :=
      integral_congr_ae (ae_restrict_of_ae ((coeFn_translate r u).fun_comp norm).symm)
    rw [heq]
    exact (setIntegral_norm_le_mul_norm S hS hvol.ne (translate r u)).trans_eq
      (by rw [norm_translate])

private theorem coeFn_setIntegral_translate (u : Lp X 2 (volume : Measure ℝ))
    (a b : ℝ) :
    ((∫ r in Ioc a b, translate r u : Lp X 2 volume) : ℝ → X) =ᵐ[volume]
      fun t => ∫ r in Ioc a b, u (t + r) := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro S hS hvol
    let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hvol⟩
    exact ((Lp.memLp _).restrict S).integrable (by norm_num)
  · intro S hS hvol
    exact (integrable_translate_prod u a b hS hvol).integral_prod_right
  · intro S hS hvol
    have htranslate : IntegrableOn (fun r => translate r u) (Ioc a b) :=
      (continuous_translate u).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [← setIntegralContinuousLinearMap_apply S hS hvol.ne]
    rw [← ContinuousLinearMap.integral_comp_comm _ htranslate]
    calc
      _ = ∫ r in Ioc a b, ∫ t in S, u (t + r) := by
        apply integral_congr_ae
        refine Eventually.of_forall fun r => ?_
        dsimp only
        rw [setIntegralContinuousLinearMap_apply]
        exact integral_congr_ae (ae_restrict_of_ae (coeFn_translate r u))
      _ = _ := integral_integral_swap (integrable_translate_prod u a b hS hvol)

private theorem coeFn_intervalIntegral_translate (u : Lp X 2 (volume : Measure ℝ))
    (a b : ℝ) :
    ((∫ r in a..b, translate r u : Lp X 2 volume) : ℝ → X) =ᵐ[volume]
      fun t => ∫ r in a..b, u (t + r) := by
  simp only [intervalIntegral]
  exact (coeFn_sub _ _).trans
    ((coeFn_setIntegral_translate u a b).sub (coeFn_setIntegral_translate u b a))

theorem coeFn_steklovAverage (h : ℝ) (u : Lp X 2 (volume : Measure ℝ)) :
    steklovAverage h u =ᵐ[volume]
      fun t => DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage h u t := by
  rw [steklovAverage]
  filter_upwards [coeFn_smul (h⁻¹) (∫ r in (0 : ℝ)..h, translate r u),
    coeFn_intervalIntegral_translate u 0 h] with t hsmul hint
  rw [hsmul, Pi.smul_apply, hint]
  congr 1
  simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := h) (⇑u) t

end MeasureTheory.Lp

open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem integral_mul_bilinear_sub_translate
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (s : ℝ) :
    2 * (∫ t, ζ t * B (f t) (f (t + s) - f t)) =
      (∫ t, (ζ (t - s) - ζ t) * B (f t) (f t)) -
        ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
  have hfshift : MemLp (fun t => f (t + s)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume s)
  have hζshift : MemLp (fun t => ζ (t - s)) ∞ volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hζ.comp_measurePreserving (measurePreserving_add_right volume (-s))
  have hint {u v : ℝ → X} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
      Integrable (fun t => B (u t) (v t)) volume :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ : ℝ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) hu hv
  have hζsq : Integrable (fun t => ζ t * B (f t) (f t)) volume :=
    (hint hf hf).mul_of_top_right hζ
  have hζsqs : Integrable (fun t => ζ t * B (f (t + s)) (f (t + s))) volume :=
    (hint hfshift hfshift).mul_of_top_right hζ
  have hζsqd : Integrable (fun t => ζ t * B (f (t + s) - f t) (f (t + s) - f t)) volume :=
    (hint (hfshift.sub hf) (hfshift.sub hf)).mul_of_top_right hζ
  have hζshsq : Integrable (fun t => ζ (t - s) * B (f t) (f t)) volume :=
    (hint hf hf).mul_of_top_right hζshift
  have hζsub : Integrable (fun t => ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t))
      volume := hζsqs.sub hζsq
  have hsymm (x y : X) : B y x = B x y := by
    exact congrArg (fun L : X →L[ℝ] X →L[ℝ] ℝ => L x y) hB
  have hnorm : ∀ t, 2 * (ζ t * B (f t) (f (t + s) - f t)) =
      ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t) -
        ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
    intro t
    simp only [map_sub, sub_apply]
    rw [hsymm (f t) (f (t + s))]
    ring
  have htranslate : (∫ t, ζ t * B (f (t + s)) (f (t + s))) =
      ∫ t, ζ (t - s) * B (f t) (f t) := by
    conv_lhs =>
      rw [← integral_add_right_eq_self (fun t => ζ t * B (f (t + s)) (f (t + s))) (-s)]
    simp only [neg_add_cancel_right, sub_eq_add_neg]
  rw [← integral_const_mul]
  calc
    _ = ∫ t, ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t) -
        ζ t * B (f (t + s) - f t) (f (t + s) - f t) :=
      integral_congr_ae (Eventually.of_forall hnorm)
    _ = (∫ t, ζ t * B (f (t + s)) (f (t + s))) - (∫ t, ζ t * B (f t) (f t)) -
        ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
      rw [integral_sub hζsub hζsqd, integral_sub hζsqs hζsq]
    _ = _ := by
      rw [htranslate, ← integral_sub hζshsq hζsq]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      ring

theorem integral_mul_bilinear_sub_translate_le
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t) (s : ℝ) :
    (∫ t, ζ t * B (f t) (f (t + s) - f t)) ≤
      (1 / 2) * ∫ t, (ζ (t - s) - ζ t) * B (f t) (f t) := by
  have hid := integral_mul_bilinear_sub_translate B hB hf hζ s
  have hn : 0 ≤ ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
    apply integral_nonneg_of_ae
    filter_upwards [hζpos] with t ht
    exact mul_nonneg ht (hBpos _)
  linarith

theorem integral_mul_bilinear_diffQuot_le
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) {s : ℝ} (hs : 0 < s) :
    (∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t))) ≤
      ((K : ℝ) / 2) * ∫ t, B (f t) (f t) := by
  have hbase := integral_mul_bilinear_sub_translate_le B hB hBpos hf hζ hζpos s
  have hdiag : Integrable (fun t => B (f t) (f t)) volume :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ : ℝ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) hf hf
  have hζshift : MemLp (fun t => ζ (t - s)) ∞ volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hζ.comp_measurePreserving (measurePreserving_add_right volume (-s))
  have hdiff : Integrable (fun t => (ζ (t - s) - ζ t) * B (f t) (f t)) volume :=
    hdiag.mul_of_top_right (hζshift.sub hζ)
  have hb : (∫ t, (ζ (t - s) - ζ t) * B (f t) (f t)) ≤
      (K : ℝ) * s * ∫ t, B (f t) (f t) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hdiff (hdiag.const_mul _)
    filter_upwards [] with t
    apply mul_le_mul_of_nonneg_right _ (hBpos _)
    have h := hζlip.dist_le_mul (t - s) t
    simp only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hs] at h
    exact (le_abs_self _).trans h
  have hid : (∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t))) =
      s⁻¹ * ∫ t, ζ t * B (f t) (f (t + s) - f t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [map_smul, smul_eq_mul]
    ring
  rw [hid]
  have hbound : (∫ t, ζ t * B (f t) (f (t + s) - f t)) ≤
      s * (((K : ℝ) / 2) * ∫ t, B (f t) (f t)) := by nlinarith
  exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)).trans_eq
    (by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul])

theorem integral_mul_bilinear_diffQuot_ge
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBneg : ∀ x, B x x ≤ 0)
    {f : ℝ → X} (hf : MemLp f 2 volume)
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) {s : ℝ} (hs : 0 < s) :
    ((K : ℝ) / 2) * (∫ t, B (f t) (f t)) ≤
      ∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t)) := by
  have hsym : (-B).flip = -B := by
    ext x y
    have h := congrArg (fun L : X →L[ℝ] X →L[ℝ] ℝ => L x y) hB
    change -B y x = -B x y
    exact congrArg Neg.neg h
  have hpos : ∀ x, 0 ≤ (-B) x x := by
    intro x
    change 0 ≤ -B x x
    exact neg_nonneg.mpr (hBneg x)
  have h := integral_mul_bilinear_diffQuot_le (-B) hsym hpos hf hζ hζpos hζlip hs
  simp only [neg_apply, mul_neg, integral_neg] at h
  linarith

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem tendsto_integral_bilinear_steklovAverage
    (A : ℝ → X →L[ℝ] Y →L[ℝ] Z)
    (hA : ∀ x y, AEStronglyMeasurable (fun t => A t x y) volume)
    {C : ℝ} (hC : ∀ᵐ t ∂volume, ‖A t‖ ≤ C)
    (u : Lp X 2 (volume : Measure ℝ)) (v : Lp Y 2 (volume : Measure ℝ)) :
    Tendsto (fun h => ∫ t, A t (u t) (steklovAverage h v t))
      (𝓝[≠] 0) (𝓝 (∫ t, A t (u t) (v t))) := by
  have h := ((MeasureTheory.continuous_integral_bilinear_lp_right A hA hC u).tendsto v).comp
    (Lp.tendsto_steklovAverage v)
  apply h.congr'
  filter_upwards [] with h
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_steklovAverage h v] with t ht
  rw [ht]

variable [CompleteSpace X]

theorem integral_bilinear_le_of_cutoff_steklov_identity
    (A D : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ x y, AEStronglyMeasurable (fun t => A t x y) volume)
    (hD : ∀ x y, AEStronglyMeasurable (fun t => D t x y) volume)
    {CA CD : ℝ} (hCA : ∀ᵐ t ∂volume, ‖A t‖ ≤ CA)
    (hCD : ∀ᵐ t ∂volume, ‖D t‖ ≤ CD)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : Lp X 2 (volume : Measure ℝ))
    {ζ : ℝ → ℝ} (hζ : MemLp ζ ∞ volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ)
    (htest : ∀ s : ℝ, 0 < s →
      (∫ t, A t (u t) (steklovAverage s u t)) =
        (∫ t, D t (u t) (steklovAverage s u t)) +
          ∫ t, ζ t * B (u t) (s⁻¹ • (u (t + s) - u t))) :
    (∫ t, A t (u t) (u t)) ≤
      (∫ t, D t (u t) (u t)) + ((K : ℝ) / 2) * ∫ t, B (u t) (u t) := by
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun _ h => ne_of_gt h)
  have hleft : Tendsto (fun s => ∫ t, A t (u t) (steklovAverage s u t))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t, A t (u t) (u t))) := (tendsto_integral_bilinear_steklovAverage A hA hCA u u).mono_left
    hfilter
  have hright := ((tendsto_integral_bilinear_steklovAverage D hD hCD u u).mono_left
    hfilter).add_const (((K : ℝ) / 2) * ∫ t, B (u t) (u t))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [htest s hs]
  exact add_le_add_right
    (integral_mul_bilinear_diffQuot_le B hB hBpos (Lp.memLp u) hζ hζpos hζlip hs) _

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
