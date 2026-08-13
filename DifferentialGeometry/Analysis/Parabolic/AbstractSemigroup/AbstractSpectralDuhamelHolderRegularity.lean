import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralDuhamel
import DifferentialGeometry.Analysis.Calculus.HilbertBasisDerivative
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeDeriv
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.HolderNorm

noncomputable section

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace InnerProductSpace BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

def abstractSpectralDuhamelHolderCorrection
    (b : HilbertBasis ι ℝ X) (lam : ι → ℝ) (F : ℝ → X) (t : ℝ) : X :=
  ∫ s in (0 : ℝ)..t,
    if s < t then
      abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
    else 0

private def abstractSpectralDuhamelHolderKernel
    (b : HilbertBasis ι ℝ X) (lam : ι → ℝ) (F : ℝ → X)
    (t τ : ℝ) : X :=
  if 0 < τ then
    abstractSpectralSemigroupDeriv b lam τ (F (t - τ) - F t)
  else 0

omit [CompleteSpace X] in
private theorem abstractSpectralDuhamelHolderCorrection_eq_kernel_integral
    (b : HilbertBasis ι ℝ X) (lam : ι → ℝ) (F : ℝ → X) (t : ℝ) :
    abstractSpectralDuhamelHolderCorrection b lam F t =
      ∫ τ in (0 : ℝ)..t,
        abstractSpectralDuhamelHolderKernel b lam F t τ := by
  rw [abstractSpectralDuhamelHolderCorrection]
  calc
    (∫ s in (0 : ℝ)..t,
        if s < t then
          abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
        else 0) =
        ∫ s in (0 : ℝ)..t,
          abstractSpectralDuhamelHolderKernel b lam F t (t - s) := by
      apply intervalIntegral.integral_congr
      intro s _
      change (if s < t then
          abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
        else 0) =
        abstractSpectralDuhamelHolderKernel b lam F t (t - s)
      by_cases hs : s < t
      · rw [if_pos hs]
        simp only [abstractSpectralDuhamelHolderKernel, if_pos (sub_pos.mpr hs)]
        congr 2
        ring_nf
      · rw [if_neg hs]
        simp only [abstractSpectralDuhamelHolderKernel,
          if_neg (not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hs)))]
    _ = ∫ τ in t - t..t - 0,
        abstractSpectralDuhamelHolderKernel b lam F t τ :=
      intervalIntegral.integral_comp_sub_left
        (fun τ : ℝ => abstractSpectralDuhamelHolderKernel b lam F t τ) t
    _ = ∫ τ in (0 : ℝ)..t,
        abstractSpectralDuhamelHolderKernel b lam F t τ := by ring_nf

theorem abstractSpectralDuhamelHolderCorrection_intervalIntegrable
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {F : ℝ → X} {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable
      (fun s : ℝ => if s < t then
        abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
        else 0) volume 0 t := by
  let G : ℝ → X := fun s =>
    if s < t then
      abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
    else 0
  let Graw : ℝ → X := fun s =>
    abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
  have hFcont : Continuous F := hF.continuous hα
  have hinner : Continuous (fun s : ℝ => (t - s, F s - F t)) :=
    (continuous_const.sub continuous_id).prodMk
      (hFcont.sub continuous_const)
  have hGraw : ContinuousOn Graw (Set.Iio t) := by
    simpa only [Graw, Function.comp_apply] using
      (abstractSpectralSemigroupDeriv_continuousOn_uncurry b hlam).comp
        hinner.continuousOn
        (fun s hs => ⟨by
          simpa using sub_pos.mpr (Set.mem_Iio.mp hs), Set.mem_univ _⟩)
  have hGmeas : AEStronglyMeasurable G volume := by
    have hp : AEStronglyMeasurable
        ((Set.Iio t).piecewise Graw (0 : ℝ → X)) volume :=
      AEStronglyMeasurable.piecewise (μ := volume) measurableSet_Iio
      (hGraw.aestronglyMeasurable measurableSet_Iio)
      aestronglyMeasurable_zero
    simpa only [G, Set.piecewise, Set.mem_Iio, Pi.zero_apply] using hp
  have hpow : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ ((α : ℝ) - 1)) volume 0 t := by
    have hbase : IntervalIntegrable
        (fun q : ℝ => q ^ ((α : ℝ) - 1)) volume 0 t :=
      intervalIntegral.intervalIntegrable_rpow' (by
        have hαR : 0 < (α : ℝ) := NNReal.coe_pos.mpr hα
        linarith)
    simpa using (hbase.comp_sub_left t).symm
  have hdom : IntervalIntegrable
      (fun s : ℝ => ((K : ℝ) / Real.exp 1) *
        (t - s) ^ ((α : ℝ) - 1)) volume 0 t :=
    hpow.const_mul ((K : ℝ) / Real.exp 1)
  rw [intervalIntegrable_iff, Set.uIoc_of_le ht.le] at hdom ⊢
  refine hdom.mono' hGmeas.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  by_cases hst : s < t
  · have hτ : 0 < t - s := sub_pos.mpr hst
    have hholder := hF.dist_le s t
    have hdist : dist s t = t - s := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
      ring
    rw [dist_eq_norm, hdist] at hholder
    simp only [if_pos hst]
    change ‖abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)‖ ≤
      ((K : ℝ) / Real.exp 1) *
      (t - s) ^ ((α : ℝ) - 1)
    calc
      ‖abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)‖ ≤
          (1 / (Real.exp 1 * (t - s))) * ‖F s - F t‖ :=
        norm_abstractSpectralSemigroupDeriv_le b hlam hτ (F s - F t)
      _ ≤ (1 / (Real.exp 1 * (t - s))) *
          ((K : ℝ) * (t - s) ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_left hholder (by positivity)
      _ = ((K : ℝ) / Real.exp 1) *
          (t - s) ^ ((α : ℝ) - 1) := by
        rw [Real.rpow_sub_one hτ.ne']
        field_simp [hτ.ne', (Real.exp_pos 1).ne']
  · have hst' : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp only [lt_self_iff_false, ↓reduceIte, norm_zero]
    exact mul_nonneg (div_nonneg K.coe_nonneg (Real.exp_pos 1).le)
      (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)

theorem abstractSpectralDuhamelHolderCorrection_continuousOn
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {F : ℝ → X} {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F) :
    ContinuousOn
      (fun t : ℝ => abstractSpectralDuhamelHolderCorrection b lam F t)
      (Set.Ioi 0) := by
  have hFcont : Continuous F := hF.continuous hα
  intro t ht
  have ht_pos : 0 < t := by simpa using ht
  let G : ℝ → ℝ → X := fun q τ =>
    abstractSpectralDuhamelHolderKernel b lam F q τ
  let bound : ℝ → ℝ := fun τ =>
    if 0 < τ then
      ((K : ℝ) / Real.exp 1) * τ ^ ((α : ℝ) - 1)
    else 0
  have hGmeas : ∀ q : ℝ,
      AEStronglyMeasurable (G q)
        (volume.restrict (Set.uIoc (-1 : ℝ) (2 * t))) := by
    intro q
    let Graw : ℝ → X := fun τ =>
      abstractSpectralSemigroupDeriv b lam τ (F (q - τ) - F q)
    have hinner : Continuous (fun τ : ℝ => (τ, F (q - τ) - F q)) :=
      continuous_id.prodMk
        ((hFcont.comp (continuous_const.sub continuous_id)).sub continuous_const)
    have hGraw : ContinuousOn Graw (Set.Ioi 0) := by
      simpa only [Graw, Function.comp_apply] using
        (abstractSpectralSemigroupDeriv_continuousOn_uncurry b hlam).comp
          hinner.continuousOn
          (fun τ hτ => ⟨hτ, Set.mem_univ _⟩)
    have hp : AEStronglyMeasurable
        ((Set.Ioi 0).piecewise Graw (0 : ℝ → X)) volume :=
      AEStronglyMeasurable.piecewise measurableSet_Ioi
        (hGraw.aestronglyMeasurable measurableSet_Ioi)
        aestronglyMeasurable_zero
    have hglobal : AEStronglyMeasurable (G q) volume := by
      simpa only [G, abstractSpectralDuhamelHolderKernel, Set.piecewise,
        Set.mem_Ioi, Pi.zero_apply] using hp
    exact hglobal.mono_measure Measure.restrict_le_self
  have hGbound : ∀ᶠ q in 𝓝 t,
      ∀ᵐ τ ∂volume.restrict (Set.uIoc (-1 : ℝ) (2 * t)),
        ‖G q τ‖ ≤ bound τ := by
    filter_upwards with q
    exact ae_of_all _ fun τ => by
      by_cases hτ : 0 < τ
      · have hholder := hF.dist_le (q - τ) q
        have hdist : dist (q - τ) q = τ := by
          rw [Real.dist_eq]
          have heq : q - τ - q = -τ := by ring
          rw [heq, abs_neg, abs_of_pos hτ]
        rw [dist_eq_norm, hdist] at hholder
        simp only [G, abstractSpectralDuhamelHolderKernel, if_pos hτ, bound]
        calc
          ‖abstractSpectralSemigroupDeriv b lam τ (F (q - τ) - F q)‖ ≤
              (1 / (Real.exp 1 * τ)) * ‖F (q - τ) - F q‖ :=
            norm_abstractSpectralSemigroupDeriv_le b hlam hτ _
          _ ≤ (1 / (Real.exp 1 * τ)) * ((K : ℝ) * τ ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_left hholder (by positivity)
          _ = ((K : ℝ) / Real.exp 1) * τ ^ ((α : ℝ) - 1) := by
            rw [Real.rpow_sub_one hτ.ne']
            field_simp [hτ.ne', (Real.exp_pos 1).ne']
      · simp only [G, abstractSpectralDuhamelHolderKernel, if_neg hτ,
          norm_zero, bound]
        exact le_rfl
  have hbound : IntervalIntegrable bound volume (-1 : ℝ) (2 * t) := by
    have hpow : IntervalIntegrable
      (fun τ : ℝ => ((K : ℝ) / Real.exp 1) *
          τ ^ ((α : ℝ) - 1)) volume 0 (2 * t) :=
      (intervalIntegral.intervalIntegrable_rpow' (by
        have hαR : 0 < (α : ℝ) := NNReal.coe_pos.mpr hα
        linarith : -1 < (α : ℝ) - 1)).const_mul ((K : ℝ) / Real.exp 1)
    have hneg : IntervalIntegrable bound volume (-1 : ℝ) 0 := by
      refine (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => (0 : ℝ)) volume (-1 : ℝ) 0).congr ?_
      intro τ hτ
      rw [Set.uIoc_of_le (by norm_num)] at hτ
      simp only [bound, if_neg (not_lt.mpr hτ.2)]
    have hpos : IntervalIntegrable bound volume 0 (2 * t) := by
      refine hpow.congr ?_
      intro τ hτ
      rw [Set.uIoc_of_le (by linarith)] at hτ
      simp only [bound, if_pos hτ.1]
    exact hneg.trans hpos
  have hGcont : ∀ᵐ τ ∂volume.restrict (Set.uIoc (-1 : ℝ) (2 * t)),
      ContinuousAt (fun q : ℝ => G q τ) t := by
    exact ae_of_all _ fun τ => by
      by_cases hτ : 0 < τ
      · have harg : Continuous (fun q : ℝ => F (q - τ) - F q) :=
          (hFcont.comp (continuous_id.sub continuous_const)).sub hFcont
        simpa only [G, abstractSpectralDuhamelHolderKernel, if_pos hτ] using
          ((abstractSpectralSemigroupDerivCLM b hlam τ hτ).continuous.comp
            harg).continuousAt
      · simpa only [G, abstractSpectralDuhamelHolderKernel, if_neg hτ] using
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : X)) t)
  have hparam := intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (X := ℝ) (E := X) (F := G) (bound := bound) (a := (-1 : ℝ))
    (b := 2 * t) (a₀ := 0) (b₀ := t) (x₀ := t) hGmeas hGbound hbound hGcont
    (by constructor <;> linarith)
    (by constructor <;> linarith)
    (by simp)
  have hdiag : ContinuousAt (fun q : ℝ => ∫ τ in (0 : ℝ)..q, G q τ) t :=
    hparam.comp_of_eq (continuousAt_id.prodMk continuousAt_id) rfl
  rw [show (fun q : ℝ => abstractSpectralDuhamelHolderCorrection b lam F q) =
      (fun q : ℝ => ∫ τ in (0 : ℝ)..q, G q τ) by
    funext q
    exact abstractSpectralDuhamelHolderCorrection_eq_kernel_integral b lam F q]
  exact hdiag.continuousWithinAt

theorem abstractSpectralDuhamelHolderCorrection_repr_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {F : ℝ → X} {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    (b.repr (abstractSpectralDuhamelHolderCorrection b lam F t) : ι → ℝ) i =
      ∫ s in (0 : ℝ)..t,
        -(lam i) * Real.exp (-(lam i) * (t - s)) *
          ((b.repr (F s) : ι → ℝ) i - (b.repr (F t) : ι → ℝ) i) := by
  let ℓ : X →L[ℝ] ℝ := innerSL (𝕜 := ℝ) (E := X) (b i)
  have hint := abstractSpectralDuhamelHolderCorrection_intervalIntegrable
    b hlam hα hF ht
  have hcomm := ℓ.intervalIntegral_comp_comm hint
  rw [b.repr_apply_apply]
  change ℓ (abstractSpectralDuhamelHolderCorrection b lam F t) = _
  rw [abstractSpectralDuhamelHolderCorrection, ← hcomm]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.le] at hs
  by_cases hst : s < t
  · simp only [if_pos hst]
    change ℓ (abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)) = _
    simp only [ℓ, innerSL_apply_apply, ← b.repr_apply_apply]
    rw [abstractSpectralSemigroupDeriv_repr_apply b hlam (sub_pos.mpr hst), map_sub]
    rfl
  · have hst' : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp

def abstractSpectralDuhamelHolderDeriv
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) (F : ℝ → X) (t : ℝ) : X :=
  abstractSpectralSemigroupDeriv b lam t u₀ +
    abstractSpectralSemigroup b hlam t (F t) +
    abstractSpectralDuhamelHolderCorrection b lam F t

theorem abstractSpectralDuhamelHolderDeriv_repr_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {K α : NNReal} (hα : 0 < α)
    (hF : HolderWith K α F) {t : ℝ} (ht : 0 < t) (i : ι) :
    (b.repr (abstractSpectralDuhamelHolderDeriv b hlam u₀ F t) : ι → ℝ) i =
      -(lam i) *
          (b.repr (abstractSpectralDuhamel b hlam u₀ F t) : ι → ℝ) i +
        (b.repr (F t) : ι → ℝ) i := by
  have hFcont : Continuous F := hF.continuous hα
  have hduhamel := abstractSpectralDuhamel_repr_apply b hlam u₀ hFcont ht.le i
  have hcorrection := abstractSpectralDuhamelHolderCorrection_repr_apply
    b hlam hα hF ht i
  have hkernel := kernelIntegral_space (lam i) t
  have hkernel' :
      (∫ s in (0 : ℝ)..t, lam i * Real.exp (-lam i * (t - s))) =
        1 - Real.exp (-lam i * t) := by
    simpa only [neg_mul] using hkernel
  simp only [abstractSpectralDuhamelHolderDeriv]
  rw [map_add, map_add]
  change
    (b.repr (abstractSpectralSemigroupDeriv b lam t u₀) : ι → ℝ) i +
        (b.repr (abstractSpectralSemigroup b hlam t (F t)) : ι → ℝ) i +
        (b.repr (abstractSpectralDuhamelHolderCorrection b lam F t) : ι → ℝ) i = _
  rw [abstractSpectralSemigroupDeriv_repr_apply b hlam ht,
    abstractSpectralSemigroup_repr_apply b hlam ht.le, hcorrection, hduhamel]
  simp only [heatDerivCoeff_def, heatCoeff_def]
  have hsplit :
      (∫ s in (0 : ℝ)..t,
        -(lam i) * Real.exp (-(lam i) * (t - s)) *
          ((b.repr (F s) : ι → ℝ) i - (b.repr (F t) : ι → ℝ) i)) =
      -(lam i) * (∫ s in (0 : ℝ)..t,
        Real.exp (-(lam i) * (t - s)) * (b.repr (F s) : ι → ℝ) i) +
      (1 - Real.exp (-(lam i) * t)) * (b.repr (F t) : ι → ℝ) i := by
    have hmode : Continuous (fun s : ℝ => (b.repr (F s) : ι → ℝ) i) := by
      simpa only [b.repr_apply_apply] using
        (innerSL (𝕜 := ℝ) (E := X) (b i)).continuous.comp hFcont
    rw [show (fun s : ℝ =>
        -(lam i) * Real.exp (-(lam i) * (t - s)) *
          ((b.repr (F s) : ι → ℝ) i - (b.repr (F t) : ι → ℝ) i)) =
      fun s => -(lam i) *
          (Real.exp (-(lam i) * (t - s)) * (b.repr (F s) : ι → ℝ) i) +
        (lam i * Real.exp (-(lam i) * (t - s))) *
          (b.repr (F t) : ι → ℝ) i from by
        funext s
        ring]
    rw [intervalIntegral.integral_add
      ((Continuous.intervalIntegrable (by fun_prop)) 0 t)
      ((Continuous.intervalIntegrable (by fun_prop)) 0 t),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, hkernel']
  rw [hsplit]
  ring

theorem abstractSpectralDuhamelHolderDeriv_continuousOn
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {K α : NNReal} (hα : 0 < α)
    (hF : HolderWith K α F) :
    ContinuousOn
      (abstractSpectralDuhamelHolderDeriv b hlam u₀ F)
      (Set.Ioi 0) := by
  have hFcont : Continuous F := hF.continuous hα
  have hsemigroup : ContinuousOn
      (fun t : ℝ => abstractSpectralSemigroup b hlam t (F t))
      (Set.Ioi 0) := by
    exact ((abstractSpectralBoundedC0Semigroup b hlam).continuousOn_uncurry).comp
      (continuousOn_id.prodMk hFcont.continuousOn)
      (fun t ht => by
        change (t, F t) ∈ Set.Ici 0 ×ˢ Set.univ
        exact ⟨Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le, Set.mem_univ _⟩)
  exact ((abstractSpectralSemigroupDeriv_continuousOn b hlam u₀).add
    hsemigroup).add
      (abstractSpectralDuhamelHolderCorrection_continuousOn b hlam hα hF)

theorem abstractSpectralDuhamel_hasDerivAt_of_holder
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {K α : NNReal} (hα : 0 < α)
    (hF : HolderWith K α F) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (abstractSpectralDuhamel b hlam u₀ F)
      (abstractSpectralDuhamelHolderDeriv b hlam u₀ F t) t := by
  have hFcont : Continuous F := hF.continuous hα
  let v : ℝ → X := fun q =>
    abstractSpectralDuhamelHolderDeriv b hlam u₀ F q
  have hv : ContinuousOn v (Set.Ioi 0) :=
    abstractSpectralDuhamelHolderDeriv_continuousOn b hlam u₀ hα hF
  change HasDerivAt (abstractSpectralDuhamel b hlam u₀ F) (v t) t
  refine hasDerivAt_of_inner_hilbertBasis b isOpen_Ioi hv ?_ ht
  intro q hq i
  have hmodal := abstractSpectralDuhamel_hasDerivAt_repr_apply
    b hlam u₀ hFcont hq i
  have hcandidate := abstractSpectralDuhamelHolderDeriv_repr_apply
    b hlam u₀ hα hF hq i
  have hcandidate' :
      ⟪b i, v q⟫_ℝ =
        -(lam i) *
            (b.repr (abstractSpectralDuhamel b hlam u₀ F q) : ι → ℝ) i +
          (b.repr (F q) : ι → ℝ) i := by
    simpa only [v, b.repr_apply_apply] using hcandidate
  have hmodal' : HasDerivAt
      (fun s : ℝ => ⟪b i, abstractSpectralDuhamel b hlam u₀ F s⟫_ℝ)
      (-(lam i) *
          (b.repr (abstractSpectralDuhamel b hlam u₀ F q) : ι → ℝ) i +
        (b.repr (F q) : ι → ℝ) i) q := by
    simpa only [b.repr_apply_apply] using hmodal
  exact hcandidate' ▸ hmodal'

theorem abstractSpectralDuhamel_contDiffOn_one_of_holder
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {K α : NNReal} (hα : 0 < α)
    (hF : HolderWith K α F) :
    ContDiffOn ℝ 1 (abstractSpectralDuhamel b hlam u₀ F) (Set.Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (abstractSpectralDuhamel_hasDerivAt_of_holder
      b hlam u₀ hα hF ht).differentiableAt.differentiableWithinAt
  · simp only [WithTop.zero_ne_top, false_implies]
  · rw [contDiffOn_zero]
    refine (abstractSpectralDuhamelHolderDeriv_continuousOn
      b hlam u₀ hα hF).congr ?_
    intro t ht
    exact (abstractSpectralDuhamel_hasDerivAt_of_holder
      b hlam u₀ hα hF ht).deriv

private def holderIccExtension
    (F : ℝ → X) (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : X :=
  F (Set.projIcc 0 T hT t)

omit [InnerProductSpace ℝ X] [CompleteSpace X] in
private theorem holderIccExtension_holderWith
    {F : ℝ → X} {T : ℝ} (hT : 0 ≤ T) {K α : NNReal}
    (hF : HolderOnWith K α F (Set.Icc 0 T)) :
    HolderWith K α (holderIccExtension F T hT) := by
  have hrestricted : HolderWith K α (Set.restrict (Set.Icc 0 T) F) :=
    hF.holderWith
  have hcomp := hrestricted.comp (LipschitzWith.projIcc hT).holderWith
  simpa [holderIccExtension] using hcomp

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] in
private theorem holderIccExtension_apply
    (F : ℝ → X) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    holderIccExtension F T hT t = F t := by
  simp only [holderIccExtension]
  rw [Set.projIcc_of_mem hT ht]

private theorem abstractSpectralDuhamel_eq_holderIccExtension
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) (F : ℝ → X) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    abstractSpectralDuhamel b hlam u₀ F t =
      abstractSpectralDuhamel b hlam u₀ (holderIccExtension F T hT) t := by
  unfold abstractSpectralDuhamel duhamel
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.1] at hs
  exact congrArg
    (fun v : X => abstractSpectralBoundedC0Semigroup b hlam (t - s) v)
    (holderIccExtension_apply F hT ⟨hs.1, hs.2.trans ht.2⟩).symm

omit [CompleteSpace X] in
private theorem abstractSpectralDuhamelHolderCorrection_eq_holderIccExtension
    (b : HilbertBasis ι ℝ X) (lam : ι → ℝ) (F : ℝ → X)
    {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    abstractSpectralDuhamelHolderCorrection b lam F t =
      abstractSpectralDuhamelHolderCorrection b lam
        (holderIccExtension F T hT) t := by
  unfold abstractSpectralDuhamelHolderCorrection
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.1] at hs
  by_cases hst : s < t
  · simp only [if_pos hst]
    rw [holderIccExtension_apply F hT ⟨hs.1, hs.2.trans ht.2⟩,
      holderIccExtension_apply F hT ht]
  · simp only [if_neg hst]

private theorem abstractSpectralDuhamelHolderDeriv_eq_holderIccExtension
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) (F : ℝ → X) {T : ℝ} (hT : 0 ≤ T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    abstractSpectralDuhamelHolderDeriv b hlam u₀ F t =
      abstractSpectralDuhamelHolderDeriv b hlam u₀
        (holderIccExtension F T hT) t := by
  unfold abstractSpectralDuhamelHolderDeriv
  rw [holderIccExtension_apply F hT ht,
    abstractSpectralDuhamelHolderCorrection_eq_holderIccExtension
      b lam F hT ht]

theorem abstractSpectralDuhamelHolderDeriv_repr_apply_of_holderOn
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {T : ℝ} {K α : NNReal}
    (hα : 0 < α) (hF : HolderOnWith K α F (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (i : ι) :
    (b.repr (abstractSpectralDuhamelHolderDeriv b hlam u₀ F t) : ι → ℝ) i =
      -(lam i) *
          (b.repr (abstractSpectralDuhamel b hlam u₀ F t) : ι → ℝ) i +
        (b.repr (F t) : ι → ℝ) i := by
  have hT : 0 ≤ T := (ht.1.trans ht.2).le
  let Fext : ℝ → X := holderIccExtension F T hT
  have hFext : HolderWith K α Fext :=
    holderIccExtension_holderWith hT hF
  have hrepr := abstractSpectralDuhamelHolderDeriv_repr_apply
    b hlam u₀ hα hFext ht.1 i
  have hFt : Fext t = F t := by
    simpa only [Fext] using
      holderIccExtension_apply F hT ⟨ht.1.le, ht.2.le⟩
  rw [← abstractSpectralDuhamelHolderDeriv_eq_holderIccExtension
      b hlam u₀ F hT ⟨ht.1.le, ht.2.le⟩,
    ← abstractSpectralDuhamel_eq_holderIccExtension
      b hlam u₀ F hT ⟨ht.1.le, ht.2.le⟩, hFt] at hrepr
  exact hrepr

theorem abstractSpectralDuhamel_hasDerivAt_of_holderOn
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {T : ℝ} {K α : NNReal}
    (hα : 0 < α) (hF : HolderOnWith K α F (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (abstractSpectralDuhamel b hlam u₀ F)
      (abstractSpectralDuhamelHolderDeriv b hlam u₀ F t) t := by
  have hT : 0 ≤ T := (ht.1.trans ht.2).le
  let Fext : ℝ → X := holderIccExtension F T hT
  have hFext : HolderWith K α Fext :=
    holderIccExtension_holderWith hT hF
  have hext := abstractSpectralDuhamel_hasDerivAt_of_holder
    b hlam u₀ hα hFext ht.1
  have hfunctions :
      abstractSpectralDuhamel b hlam u₀ F =ᶠ[nhds t]
        abstractSpectralDuhamel b hlam u₀ Fext := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with q hq
    exact abstractSpectralDuhamel_eq_holderIccExtension
      b hlam u₀ F hT ⟨hq.1.le, hq.2.le⟩
  have hderiv :
      abstractSpectralDuhamelHolderDeriv b hlam u₀ F t =
        abstractSpectralDuhamelHolderDeriv b hlam u₀ Fext t :=
    abstractSpectralDuhamelHolderDeriv_eq_holderIccExtension
      b hlam u₀ F hT ⟨ht.1.le, ht.2.le⟩
  exact (hext.congr_of_eventuallyEq hfunctions).congr_deriv hderiv.symm

theorem abstractSpectralDuhamelHolderDeriv_continuousOn_of_holderOn
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {T : ℝ} {K α : NNReal}
    (hα : 0 < α) (hF : HolderOnWith K α F (Set.Icc 0 T)) :
    ContinuousOn
      (abstractSpectralDuhamelHolderDeriv b hlam u₀ F)
      (Set.Ioo 0 T) := by
  rcases le_total 0 T with hT | hT
  · let Fext : ℝ → X := holderIccExtension F T hT
    have hFext : HolderWith K α Fext :=
      holderIccExtension_holderWith hT hF
    have hcont : ContinuousOn
        (abstractSpectralDuhamelHolderDeriv b hlam u₀ Fext)
        (Set.Ioo 0 T) :=
      (abstractSpectralDuhamelHolderDeriv_continuousOn
        b hlam u₀ hα hFext).mono Set.Ioo_subset_Ioi_self
    refine hcont.congr ?_
    intro t ht
    simpa only [Fext] using
      abstractSpectralDuhamelHolderDeriv_eq_holderIccExtension
        b hlam u₀ F hT ⟨ht.1.le, ht.2.le⟩
  · intro t ht
    exact False.elim ((not_lt_of_ge hT) (ht.1.trans ht.2))

theorem abstractSpectralDuhamel_contDiffOn_one_of_holderOn
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {T : ℝ} {K α : NNReal}
    (hα : 0 < α) (hF : HolderOnWith K α F (Set.Icc 0 T)) :
    ContDiffOn ℝ 1 (abstractSpectralDuhamel b hlam u₀ F) (Set.Ioo 0 T) := by
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (abstractSpectralDuhamel_hasDerivAt_of_holderOn
      b hlam u₀ hα hF ht).differentiableAt.differentiableWithinAt
  · simp only [WithTop.zero_ne_top, false_implies]
  · rw [contDiffOn_zero]
    refine (abstractSpectralDuhamelHolderDeriv_continuousOn_of_holderOn
      b hlam u₀ hα hF).congr ?_
    intro t ht
    exact (abstractSpectralDuhamel_hasDerivAt_of_holderOn
      b hlam u₀ hα hF ht).deriv

end Parabolic
end Analysis
end DifferentialGeometry

end
