import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [SFinite μ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => Lp ℝ 2 (μ.prod (volume : Measure E))

private theorem measurePreserving_spatialTranslate (v : E) :
    MeasurePreserving (fun p : Z × E => (p.1, p.2 + v)) (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).prod (measurePreserving_add_right volume v)

def spatialTranslate (v : E) (u : X) : X :=
  compMeasurePreserving _ (measurePreserving_spatialTranslate v) u

theorem coeFn_spatialTranslate (v : E) (u : X) :
    spatialTranslate v u =ᵐ[μ.prod volume] fun p => u (p.1, p.2 + v) :=
  coeFn_compMeasurePreserving u (measurePreserving_spatialTranslate v)

@[simp] theorem norm_spatialTranslate (v : E) (u : X) : ‖spatialTranslate v u‖ = ‖u‖ :=
  norm_compMeasurePreserving u _

@[simp] theorem spatialTranslate_zero (u : X) : spatialTranslate 0 u = u := by
  simp only [spatialTranslate, add_zero, Prod.mk.eta]
  exact compMeasurePreserving_id_apply u

def spatialSteklovAverage (v : E) (h : ℝ) (u : X) : X :=
  h⁻¹ • ∫ r in (0 : ℝ)..h, spatialTranslate (r • v) u

theorem norm_spatialSteklovAverage_le (v : E) (h : ℝ) (u : X) :
    ‖spatialSteklovAverage v h u‖ ≤ ‖u‖ := by
  by_cases hh : h = 0
  · simp [spatialSteklovAverage, hh]
  have hhabs : |h| ≠ 0 := abs_ne_zero.mpr hh
  calc
    ‖spatialSteklovAverage v h u‖ = |h|⁻¹ * ‖∫ r in (0 : ℝ)..h, spatialTranslate (r • v) u‖ := by
      rw [spatialSteklovAverage, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |h|⁻¹ * (‖u‖ * |h|) := by
      gcongr
      simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
        (fun r _ => (norm_spatialTranslate (r • v) u).le)
    _ = ‖u‖ := by field_simp

end MeasureTheory.Lp

namespace MeasureTheory.Lp

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "X" => Lp ℝ 2 (μ.prod (volume : Measure E))

theorem continuous_spatialTranslate (u : X) : Continuous (fun v : E => spatialTranslate v u) := by
  let g : C(E, C(ℝ × E, ℝ × E)) := (ContinuousMap.mk
    (fun p : E × (ℝ × E) => (p.2.1, p.2.2 + p.1))
    ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_snd.comp continuous_snd).add continuous_fst))).curry
  exact continuous_const.compMeasurePreservingLp g.continuous
    (fun v => measurePreserving_spatialTranslate v) (by norm_num)

theorem tendsto_spatialSteklovAverage (v : E) (u : X) :
    Tendsto (fun h => spatialSteklovAverage v h u) (𝓝[≠] 0) (𝓝 u) := by
  have hc : Continuous (fun r : ℝ => spatialTranslate (r • v) u) :=
    (continuous_spatialTranslate u).comp (continuous_id.smul continuous_const)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [zero_smul, spatialTranslate_zero, spatialSteklovAverage, zero_add,
    intervalIntegral.integral_same, sub_zero] using hd.tendsto_slope_zero

end MeasureTheory.Lp


namespace MeasureTheory.Lp

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Y" => ℝ × E
local notation "ν" => μ.prod (volume : Measure E)
local notation "X" => Lp ℝ 2 ν

private def setIntegralContinuousLinearMap (S : Set Y) (hS : MeasurableSet S)
    (hvol : ν S ≠ ∞) : X →L[ℝ] ℝ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing ν 2 2 (indicatorConstLp 2 hS hvol (1 : ℝ))

omit [IsLocallyFiniteMeasure μ] in
private theorem setIntegralContinuousLinearMap_apply (S : Set Y) (hS : MeasurableSet S)
    (hvol : ν S ≠ ∞) (u : X) :
    setIntegralContinuousLinearMap S hS hvol u = ∫ t in S, u t ∂ν := by
  rw [setIntegralContinuousLinearMap, ContinuousLinearMap.lpPairing_eq_integral]
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hvol) (c := (1 : ℝ))] with t ht
  rw [ContinuousLinearMap.lsmul_apply, ht]
  by_cases htS : t ∈ S
  · simp only [indicator_of_mem htS, one_smul]
  · simp only [indicator_of_notMem htS, zero_smul]

omit [IsLocallyFiniteMeasure μ] in
private theorem setIntegral_norm_le_mul_norm (S : Set Y) (hS : MeasurableSet S)
    (hvol : ν S ≠ ∞) (u : X) :
    (∫ t in S, ‖u t‖ ∂ν) ≤ ‖setIntegralContinuousLinearMap S hS hvol‖ * ‖u‖ := by
  let v : X := (Lp.memLp u).norm.toLp (fun t => ‖u t‖)
  have hnorm : ‖v‖ = ‖u‖ := by
    rw [show v = (Lp.memLp u).norm.toLp (fun t => ‖u t‖) from rfl, Lp.norm_toLp, eLpNorm_norm]
    rfl
  have heq : (∫ t in S, ‖u t‖ ∂ν) = setIntegralContinuousLinearMap S hS hvol v := by
    rw [setIntegralContinuousLinearMap_apply]
    exact integral_congr_ae (ae_restrict_of_ae (MemLp.coeFn_toLp (Lp.memLp u).norm).symm)
  rw [heq]
  calc
    _ ≤ ‖setIntegralContinuousLinearMap S hS hvol v‖ := le_abs_self _
    _ ≤ ‖setIntegralContinuousLinearMap S hS hvol‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hnorm]

private theorem integrable_translate_prod (u : X)
    (v : E) (a b : ℝ) {S : Set Y} (hS : MeasurableSet S) (hvol : ν S < ∞) :
    Integrable (fun q : ℝ × Y => u (q.2.1, q.2.2 + q.1 • v))
      ((volume.restrict (Ioc a b)).prod ((ν).restrict S)) := by
  let : IsFiniteMeasure ((ν).restrict S) := ⟨by simpa using hvol⟩
  have hmeas : StronglyMeasurable (fun q : ℝ × Y => u (q.2.1, q.2.2 + q.1 • v)) :=
    (Lp.stronglyMeasurable u).comp_measurable ((measurable_fst.comp measurable_snd).prodMk ((measurable_snd.comp measurable_snd).add (measurable_fst.smul_const v)))
  apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun r =>
      (((Lp.memLp u).comp_measurePreserving ((MeasurePreserving.id μ).prod (measurePreserving_add_right volume (r • v)))).restrict S).integrable (by norm_num)
  · apply Integrable.mono' (integrable_const (‖setIntegralContinuousLinearMap S hS hvol.ne‖ * ‖u‖))
      hmeas.norm.aestronglyMeasurable.integral_prod_right'
    refine Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (integral_nonneg (μ := (ν).restrict S) fun t : Y => norm_nonneg (u (t.1, t.2 + r • v)))]
    have heq : (∫ t in S, ‖u (t.1, t.2 + r • v)‖ ∂ν) = ∫ t in S, ‖spatialTranslate (r • v) u t‖ ∂ν :=
      integral_congr_ae (ae_restrict_of_ae ((coeFn_spatialTranslate (r • v) u).fun_comp norm).symm)
    rw [heq]
    exact (setIntegral_norm_le_mul_norm S hS hvol.ne (spatialTranslate (r • v) u)).trans_eq
      (by rw [norm_spatialTranslate])

private theorem coeFn_setIntegral_translate (u : X)
    (v : E) (a b : ℝ) :
    ((∫ r in Ioc a b, spatialTranslate (r • v) u : X) : Y → ℝ) =ᵐ[ν]
      fun t => ∫ r in Ioc a b, u (t.1, t.2 + r • v) := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro S hS hvol
    let : IsFiniteMeasure ((ν).restrict S) := ⟨by simpa using hvol⟩
    exact ((Lp.memLp _).restrict S).integrable (by norm_num)
  · intro S hS hvol
    exact (integrable_translate_prod u v a b hS hvol).integral_prod_right
  · intro S hS hvol
    have htranslate : IntegrableOn (fun r => spatialTranslate (r • v) u) (Ioc a b) :=
      ((continuous_spatialTranslate u).comp (continuous_id.smul continuous_const)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    rw [← setIntegralContinuousLinearMap_apply S hS hvol.ne]
    rw [← ContinuousLinearMap.integral_comp_comm _ htranslate]
    calc
      _ = ∫ r in Ioc a b, ∫ t in S, u (t.1, t.2 + r • v) ∂ν := by
        apply integral_congr_ae
        refine Eventually.of_forall fun r => ?_
        dsimp only
        rw [setIntegralContinuousLinearMap_apply]
        exact integral_congr_ae (ae_restrict_of_ae (coeFn_spatialTranslate (r • v) u))
      _ = _ := integral_integral_swap (integrable_translate_prod u v a b hS hvol)

private theorem coeFn_intervalIntegral_translate (u : X)
    (v : E) (a b : ℝ) :
    ((∫ r in a..b, spatialTranslate (r • v) u : X) : Y → ℝ) =ᵐ[ν]
      fun t => ∫ r in a..b, u (t.1, t.2 + r • v) := by
  simp only [intervalIntegral]
  exact (coeFn_sub _ _).trans
    ((coeFn_setIntegral_translate u v a b).sub (coeFn_setIntegral_translate u v b a))

theorem coeFn_spatialSteklovAverage (v : E) (h : ℝ) (u : X) :
    spatialSteklovAverage v h u =ᵐ[ν]
      fun z => h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1, z.2 + r • v) := by
  rw [spatialSteklovAverage]
  filter_upwards [coeFn_smul (h⁻¹) (∫ r in (0 : ℝ)..h, spatialTranslate (r • v) u),
    coeFn_intervalIntegral_translate u v 0 h] with z hsmul hint
  rw [hsmul, Pi.smul_apply, hint, smul_eq_mul]

end MeasureTheory.Lp
