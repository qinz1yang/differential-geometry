import DifferentialGeometry.Analysis.Integration.Gaussian.VolumeTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set MeasureTheory intervalIntegral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

private def reducedCostGrowthIntegrand (Lm LM s : ℝ) : ℝ :=
  ((8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) + 4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) +
      3 * s ^ ((1 / 4) : ℝ)) * Real.sqrt (Lm + 1) +
    Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)

private def reducedCostGrowthMajor : ℝ :=
  (8 + Real.sqrt 3) * 4 + 4 * Real.sqrt 3 * (4 / 3) + 3 * (4 / 5)

private def reducedCostGrowthMinor : ℝ := Real.sqrt 3 * 4

private theorem integral_rpow_neg_three_quarters :
    (∫ s in (0 : ℝ)..1, s ^ (-(3 / 4) : ℝ)) = 4 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4)))]
  norm_num

private theorem integral_rpow_neg_one_quarter :
    (∫ s in (0 : ℝ)..1, s ^ (-(1 / 4) : ℝ)) = 4 / 3 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 4)))]
  norm_num

private theorem integral_rpow_one_quarter :
    (∫ s in (0 : ℝ)..1, s ^ ((1 / 4) : ℝ)) = 4 / 5 := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < (1 / 4)))]
  norm_num

private theorem intervalIntegrable_rpow_neg_three_quarters :
    IntervalIntegrable (fun s : ℝ => s ^ (-(3 / 4) : ℝ)) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(3 / 4))

private theorem intervalIntegrable_rpow_neg_one_quarter :
    IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 4) : ℝ)) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 4))

private theorem intervalIntegrable_rpow_one_quarter :
    IntervalIntegrable (fun s : ℝ => s ^ ((1 / 4) : ℝ)) volume 0 1 :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < (1 / 4))

private theorem integral_reducedCostGrowth_sum :
    (∫ s in (0 : ℝ)..1, ((8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
        4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ))) =
      (8 + Real.sqrt 3) * 4 + 4 * Real.sqrt 3 * (4 / 3) + 3 * (4 / 5) := by
  have h1 : IntervalIntegrable (fun s : ℝ => (8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ))
      volume 0 1 := intervalIntegrable_rpow_neg_three_quarters.const_mul _
  have h2 : IntervalIntegrable (fun s : ℝ => 4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ))
      volume 0 1 := intervalIntegrable_rpow_neg_one_quarter.const_mul _
  have h3 : IntervalIntegrable (fun s : ℝ => 3 * s ^ ((1 / 4) : ℝ)) volume 0 1 :=
    intervalIntegrable_rpow_one_quarter.const_mul _
  rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_rpow_neg_three_quarters,
    integral_rpow_neg_one_quarter, integral_rpow_one_quarter]

private theorem integral_reducedCostGrowth_tail {LM : ℝ} :
    (∫ s in (0 : ℝ)..1, Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)) =
      Real.sqrt 3 * 4 * Real.sqrt (LM + 1) := by
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    integral_rpow_neg_three_quarters]

private theorem integral_reducedCostGrowthIntegrand {Lm LM : ℝ} :
    (∫ s in (0 : ℝ)..1, reducedCostGrowthIntegrand Lm LM s) =
      reducedCostGrowthMajor * Real.sqrt (Lm + 1) +
        reducedCostGrowthMinor * Real.sqrt (LM + 1) := by
  have hsum : IntervalIntegrable
      (fun s : ℝ => (8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
        4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) volume 0 1 :=
    ((intervalIntegrable_rpow_neg_three_quarters.const_mul _).add
      (intervalIntegrable_rpow_neg_one_quarter.const_mul _)).add
      (intervalIntegrable_rpow_one_quarter.const_mul _)
  have htail : IntervalIntegrable
      (fun s : ℝ => Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)) volume 0 1 :=
    (intervalIntegrable_rpow_neg_three_quarters.const_mul _).mul_const _
  simp only [reducedCostGrowthIntegrand]
  rw [intervalIntegral.integral_add (hsum.mul_const (Real.sqrt (Lm + 1))) htail,
    intervalIntegral.integral_mul_const, integral_reducedCostGrowth_tail,
    integral_reducedCostGrowth_sum]
  rfl

private theorem intervalIntegrable_reducedCostGrowthIntegrand {Lm LM : ℝ} :
    IntervalIntegrable (reducedCostGrowthIntegrand Lm LM) volume 0 1 := by
  have hsum : IntervalIntegrable
      (fun s : ℝ => (8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
        4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) volume 0 1 :=
    ((intervalIntegrable_rpow_neg_three_quarters.const_mul _).add
      (intervalIntegrable_rpow_neg_one_quarter.const_mul _)).add
      (intervalIntegrable_rpow_one_quarter.const_mul _)
  have htail : IntervalIntegrable
      (fun s : ℝ => Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)) volume 0 1 :=
    (intervalIntegrable_rpow_neg_three_quarters.const_mul _).mul_const _
  exact (hsum.mul_const (Real.sqrt (Lm + 1))).add htail

private theorem reducedCostGrowthMajor_sq_add_minor_sq_le :
    reducedCostGrowthMajor ^ 2 + reducedCostGrowthMinor ^ 2 ≤ 4608 := by
  have h3lt : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h3nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hmajor_lt : reducedCostGrowthMajor < 54 := by
    dsimp only [reducedCostGrowthMajor]
    nlinarith [h3lt, h3nn]
  have hmajor_nn : 0 ≤ reducedCostGrowthMajor := by
    dsimp only [reducedCostGrowthMajor]
    nlinarith [h3nn]
  have hminor_lt : reducedCostGrowthMinor < 7 := by
    dsimp only [reducedCostGrowthMinor]
    have h : Real.sqrt 3 < 7 / 4 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7 / 4)]
      norm_num
    nlinarith [h, h3nn]
  have hminor_nn : 0 ≤ reducedCostGrowthMinor := by
    dsimp only [reducedCostGrowthMinor]
    nlinarith [h3nn]
  nlinarith [hmajor_lt, hmajor_nn, hminor_lt, hminor_nn]

private theorem sq_le_of_growthIntegrand {snd speed : ℝ → ℝ} {Lm LM : ℝ}
    (hLm : 0 ≤ Lm) (hLM : 0 ≤ LM)
    (hcont : ContinuousOn snd (Icc 0 1))
    (hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt snd (speed s) s)
    (hint : IntervalIntegrable speed volume 0 1)
    (hbound : ∀ s ∈ Ioo (0 : ℝ) 1, |speed s| ≤ reducedCostGrowthIntegrand Lm LM s) :
    (snd 1 - snd 0) ^ 2 ≤ 9216 * (LM + 1 + Lm) := by
  have hftc : (∫ s in (0 : ℝ)..1, speed s) = snd 1 - snd 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have habs : |snd 1 - snd 0| ≤ ∫ s in (0 : ℝ)..1, |speed s| := by
    rw [← hftc]
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := speed) (a := 0) (b := 1)
        (by norm_num : (0 : ℝ) ≤ 1)
  have hmono : (∫ s in (0 : ℝ)..1, |speed s|) ≤
      ∫ s in (0 : ℝ)..1, reducedCostGrowthIntegrand Lm LM s :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := 0) (b := 1) (by norm_num)
      hint.abs intervalIntegrable_reducedCostGrowthIntegrand hbound
  have hle : |snd 1 - snd 0| ≤ reducedCostGrowthMajor * Real.sqrt (Lm + 1) +
      reducedCostGrowthMinor * Real.sqrt (LM + 1) := by
    have h := habs.trans hmono
    rwa [integral_reducedCostGrowthIntegrand] at h
  have hnonneg : 0 ≤ reducedCostGrowthMajor * Real.sqrt (Lm + 1) +
      reducedCostGrowthMinor * Real.sqrt (LM + 1) := by
    have hmajor : 0 ≤ reducedCostGrowthMajor := by
      dsimp only [reducedCostGrowthMajor]
      nlinarith [Real.sqrt_nonneg 3]
    have hminor : 0 ≤ reducedCostGrowthMinor := by
      dsimp only [reducedCostGrowthMinor]
      nlinarith [Real.sqrt_nonneg 3]
    positivity
  have hsqLm : (Real.sqrt (Lm + 1)) ^ 2 = Lm + 1 := Real.sq_sqrt (by linarith)
  have hsqLM : (Real.sqrt (LM + 1)) ^ 2 = LM + 1 := Real.sq_sqrt (by linarith)
  have hcs : (reducedCostGrowthMajor * Real.sqrt (Lm + 1) +
      reducedCostGrowthMinor * Real.sqrt (LM + 1)) ^ 2 ≤
      (reducedCostGrowthMajor ^ 2 + reducedCostGrowthMinor ^ 2) * (LM + Lm + 2) := by
    nlinarith [sq_nonneg (reducedCostGrowthMajor * Real.sqrt (LM + 1) -
      reducedCostGrowthMinor * Real.sqrt (Lm + 1)), hsqLm, hsqLM]
  have ht : 0 ≤ LM + Lm := by linarith
  have hlast : (reducedCostGrowthMajor ^ 2 + reducedCostGrowthMinor ^ 2) * (LM + Lm + 2) ≤
      9216 * (LM + 1 + Lm) := by
    have h1 : (reducedCostGrowthMajor ^ 2 + reducedCostGrowthMinor ^ 2) * (LM + Lm) ≤
        4608 * (LM + Lm) :=
      mul_le_mul_of_nonneg_right reducedCostGrowthMajor_sq_add_minor_sq_le ht
    have h2 : (4608 : ℝ) * (LM + Lm) ≤ 9216 * (LM + Lm) := by nlinarith [ht]
    have h3 : (reducedCostGrowthMajor ^ 2 + reducedCostGrowthMinor ^ 2) * 2 ≤ 9216 := by
      nlinarith [reducedCostGrowthMajor_sq_add_minor_sq_le]
    nlinarith [h1, h2, h3]
  calc
    (snd 1 - snd 0) ^ 2 ≤
        (reducedCostGrowthMajor * Real.sqrt (Lm + 1) +
          reducedCostGrowthMinor * Real.sqrt (LM + 1)) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hnonneg]
      exact hle
    _ ≤ (reducedCostGrowthMajor ^ 2 + reducedCostGrowthMinor ^ 2) * (LM + Lm + 2) := hcs
    _ ≤ 9216 * (LM + 1 + Lm) := hlast

section GradientEstimate

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance reducedCostGradientTopology : TopologicalSpace F.M := F.topology
local instance reducedCostGradientCharted : ChartedSpace H F.M := F.charted
local instance reducedCostGradientSmooth : IsManifold I ∞ F.M := F.smooth
local instance reducedCostGradientT2 : T2Space F.M := F.t2
local instance reducedCostGradientSigma : SigmaCompactSpace F.M := F.sigmaCompact

def ReducedCostGradientBound
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (p : F.M) {tau : ℝ}, 0 < tau → ∀ Z : TangentSpace I p,
      (Z, tau) ∈ lMinDomain (I := I) (M := F.M) F.S 0 p →
        (F.S.base.metric (-tau)).inner (lExp F.S 0 p Z tau)
            (gradientFun (I := I) (F.S.base.metric (-tau))
              (fun y : F.M => redLength F.S 0 p y tau) (lExp F.S 0 p Z tau))
            (gradientFun (I := I) (F.S.base.metric (-tau))
              (fun y : F.M => redLength F.S 0 p y tau) (lExp F.S 0 p Z tau)) +
          F.S.scalar (-tau) (lExp F.S 0 p Z tau) ≤
        3 * redLength F.S 0 p (lExp F.S 0 p Z tau) tau / tau

theorem ReducedCostGradientBound.gradient_inner_self_le
    (h : ReducedCostGradientBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p : F.M) {tau : ℝ} (htau : 0 < tau) {Z : TangentSpace I p}
    (hZ : (Z, tau) ∈ lMinDomain (I := I) (M := F.M) F.S 0 p) :
    (F.S.base.metric (-tau)).inner (lExp F.S 0 p Z tau)
        (gradientFun (I := I) (F.S.base.metric (-tau))
          (fun y : F.M => redLength F.S 0 p y tau) (lExp F.S 0 p Z tau))
        (gradientFun (I := I) (F.S.base.metric (-tau))
          (fun y : F.M => redLength F.S 0 p y tau) (lExp F.S 0 p Z tau)) ≤
      3 * redLength F.S 0 p (lExp F.S 0 p Z tau) tau / tau := by
  have hbound := h hF hdim p htau Z hZ
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  have hmem : -tau ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr (by linarith)
  have hscalar : 0 ≤ F.S.scalar (-tau) (lExp F.S 0 p Z tau) := (hC (-tau) hmem _).1
  linarith

end GradientEstimate

section DistanceGrowth

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance reducedCostGrowthTopology : TopologicalSpace F.M := F.topology
local instance reducedCostGrowthCharted : ChartedSpace H F.M := F.charted
local instance reducedCostGrowthSmooth : IsManifold I ∞ F.M := F.smooth
local instance reducedCostGrowthT2 : T2Space F.M := F.t2
local instance reducedCostGrowthSigma : SigmaCompactSpace F.M := F.sigmaCompact

def ReducedCostDistanceGrowth
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x a b : F.M) {tau : ℝ}, 0 < tau →
      redLength F.S 0 x b tau ≤ redLength F.S 0 x a tau →
      1 + redLength F.S 0 x b tau <
          collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau →
        ∃ (gamma₁ gamma₂ : ℝ → F.M) (speed : ℝ → ℝ),
          gamma₁ 0 = x ∧ gamma₂ 0 = x ∧ gamma₁ 1 = a ∧ gamma₂ 1 = b ∧
          ContinuousOn (fun s : ℝ => (Real.sqrt tau)⁻¹ *
            (riemannianEDistOf (F.S.base.metric (-(tau * s))) (gamma₁ s) (gamma₂ s)).toReal)
            (Icc 0 1) ∧
          (∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun r : ℝ => (Real.sqrt tau)⁻¹ *
            (riemannianEDistOf (F.S.base.metric (-(tau * r))) (gamma₁ r) (gamma₂ r)).toReal)
            (speed s) s) ∧
          IntervalIntegrable speed volume 0 1 ∧
          ∀ s ∈ Ioc (0 : ℝ) 1, |speed s| ≤
            ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) *
                s ^ (-(3 / 4) : ℝ) +
              4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) *
              Real.sqrt (redLength F.S 0 x b tau + 1) +
            Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) *
              Real.sqrt (redLength F.S 0 x a tau + 1)

private theorem sq_dist_le_of_growth_data {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {x a b : F.M} {tau : ℝ} (htau : 0 < tau)
    (hwit : ∃ (gamma₁ gamma₂ : ℝ → F.M) (speed : ℝ → ℝ),
      gamma₁ 0 = x ∧ gamma₂ 0 = x ∧ gamma₁ 1 = a ∧ gamma₂ 1 = b ∧
      ContinuousOn (fun s : ℝ => (Real.sqrt tau)⁻¹ *
        (riemannianEDistOf (F.S.base.metric (-(tau * s))) (gamma₁ s) (gamma₂ s)).toReal)
        (Icc 0 1) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun r : ℝ => (Real.sqrt tau)⁻¹ *
        (riemannianEDistOf (F.S.base.metric (-(tau * r))) (gamma₁ r) (gamma₂ r)).toReal)
        (speed s) s) ∧
      IntervalIntegrable speed volume 0 1 ∧
      ∀ s ∈ Ioc (0 : ℝ) 1, |speed s| ≤ reducedCostGrowthIntegrand
        (redLength F.S 0 x b tau) (redLength F.S 0 x a tau) s) :
    ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 ≤
      9216 * tau * (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau) := by
  obtain ⟨gamma₁, gamma₂, speed, h0₁, h0₂, h1₁, h1₂, hcont, hderiv, hint, hbound⟩ := hwit
  have hscalar : ∀ s ∈ Icc 0 tau, ∀ y : F.M, 0 ≤ F.S.scalar (0 - s) y := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro s hs y
    have hmem : -s ∈ ancientTimeInterval.carrier := by
      rw [ancientTimeInterval_carrier]
      exact Set.mem_Iic.mpr (by linarith [hs.1])
    simpa only [zero_sub] using (hC (-s) hmem y).1
  have hLm : 0 ≤ redLength F.S 0 x b tau := by
    rw [redLength]
    exact div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le hscalar x b) (by positivity)
  have hLM : 0 ≤ redLength F.S 0 x a tau := by
    rw [redLength]
    exact div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le hscalar x a) (by positivity)
  have hsq := sq_le_of_growthIntegrand hLm hLM hcont hderiv hint
    (fun s hs => hbound s ⟨hs.1, hs.2.le⟩)
  have hU0 : (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-(tau * 0))) (gamma₁ 0) (gamma₂ 0)).toReal = 0 := by
    simp only [h0₁, h0₂]
    rw [riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
  have hU1 : (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-(tau * 1))) (gamma₁ 1) (gamma₂ 1)).toReal =
      (Real.sqrt tau)⁻¹ * (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal := by
    simp only [h1₁, h1₂, mul_one]
  have hclosed : ((Real.sqrt tau)⁻¹ * (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 ≤
      9216 * (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau) := by
    rw [hU0, hU1] at hsq
    simpa only [sub_zero] using hsq
  have hscale : tau * ((Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 =
      ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt htau.le]
    field_simp
  calc
    ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 =
        tau * ((Real.sqrt tau)⁻¹ *
          (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 := hscale.symm
    _ ≤ tau * (9216 * (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau)) :=
      mul_le_mul_of_nonneg_left hclosed htau.le
    _ = 9216 * tau * (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau) := by ring

theorem reducedCost_two_point_of_near_regime {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) {c : ℝ}
    (hnear : c * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau ≤
      1 + lCost F.S 0 p p tau / (2 * Real.sqrt tau)) :
    c * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
        lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
      lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hscalar : ∀ s ∈ Icc 0 tau, ∀ y : F.M, 0 ≤ F.S.scalar (0 - s) y := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro s hs y
    have hmem : -s ∈ ancientTimeInterval.carrier := by
      rw [ancientTimeInterval_carrier]
      exact Set.mem_Iic.mpr (by linarith [hs.1])
    simpa only [zero_sub] using (hC (-s) hmem y).1
  have hother : 0 ≤ lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
    div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le hscalar p q) (by positivity)
  linarith

private theorem reducedCost_two_point_of_distance_bound
    (p q : F.M) {tau : ℝ} (htau : 0 < tau)
    (h : ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 ≤
      9216 * tau * (redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau)) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hchi : collapsedVolumeChi = (9216 : ℝ)⁻¹ := by norm_num [collapsedVolumeChi]
  have hkey : collapsedVolumeChi *
      ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau ≤
      redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau := by
    rw [hchi, div_le_iff₀ htau]
    calc (9216 : ℝ)⁻¹ * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 ≤
        (9216 : ℝ)⁻¹ * (9216 * tau *
          (redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau)) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau) * tau := by
          field_simp
  have hmain : collapsedVolumeChi *
      ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      redLength F.S 0 p p tau ≤ redLength F.S 0 p q tau := by
    linarith [hkey]
  simpa only [redLength] using hmain

theorem ancientKappaThree_reducedCost_two_point_of_distanceGrowth
    (hgrowth : ReducedCostDistanceGrowth (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hcoef : 4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3 = 8 + Real.sqrt 3 := by
    rw [hdim]
    norm_num
  have hdist : (riemannianEDistOf (F.S.base.metric (-tau)) q p).toReal =
      (riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal := by
    rw [riemannianEDistOf_comm]
  rcases le_total (redLength F.S 0 p q tau) (redLength F.S 0 p p tau) with hle | hle
  · by_cases hfar : 1 + redLength F.S 0 p p tau < collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau
    · have hfar' : 1 + redLength F.S 0 p q tau < collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau := by linarith
      have hdata := sq_dist_le_of_growth_data (I := I) F hF (x := p) (a := p) (b := q) htau ?_
      · refine reducedCost_two_point_of_distance_bound (I := I) F p q htau ?_
        exact hdata
      · obtain ⟨gamma₁, gamma₂, speed, h0₁, h0₂, h1₁, h1₂, hcont, hderiv, hint, hbound⟩ :=
          hgrowth hF hdim p p q htau hle hfar'
        exact ⟨gamma₁, gamma₂, speed, h0₁, h0₂, h1₁, h1₂, hcont, hderiv, hint,
          fun s hs => by
            have := hbound s hs
            simpa only [reducedCostGrowthIntegrand, hcoef] using this⟩
    · exact reducedCost_two_point_of_near_regime (I := I) F hF p q htau (le_of_not_gt hfar)
  · by_cases hfar : 1 + redLength F.S 0 p p tau < collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau
    · have hfar' : 1 + redLength F.S 0 p p tau < collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) q p).toReal) ^ 2 / tau := by
        rw [hdist]
        exact hfar
      have hdata := sq_dist_le_of_growth_data (I := I) F hF (x := p) (a := q) (b := p) htau ?_
      · refine reducedCost_two_point_of_distance_bound (I := I) F p q htau ?_
        rw [hdist] at hdata
        calc ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 ≤
            9216 * tau * (redLength F.S 0 p q tau + 1 + redLength F.S 0 p p tau) := hdata
          _ = 9216 * tau * (redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau) := by ring
      · obtain ⟨gamma₁, gamma₂, speed, h0₁, h0₂, h1₁, h1₂, hcont, hderiv, hint, hbound⟩ :=
          hgrowth hF hdim p q p htau hle hfar'
        exact ⟨gamma₁, gamma₂, speed, h0₁, h0₂, h1₁, h1₂, hcont, hderiv, hint,
          fun s hs => by
            have := hbound s hs
            simpa only [reducedCostGrowthIntegrand, hcoef] using this⟩
    · exact reducedCost_two_point_of_near_regime (I := I) F hF p q htau (le_of_not_gt hfar)

end DistanceGrowth

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
