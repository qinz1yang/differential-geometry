import DifferentialGeometry.Analysis.Integration.Gaussian.VolumeTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostDistanceGrowth
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set MeasureTheory intervalIntegral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

section Numeric

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

private def growthMajor : ℝ := (8 + Real.sqrt 3) * 4 + 4 * Real.sqrt 3 * (4 / 3) + 3 * (4 / 5)

private def growthMinor : ℝ := Real.sqrt 3 * 4

private theorem intervalIntegrable_growthSum :
    IntervalIntegrable
      (fun s : ℝ => (8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
        4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) volume 0 1 :=
  (((intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(3 / 4))).const_mul _).add
    ((intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(1 / 4))).const_mul _)).add
    ((intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < (1 / 4))).const_mul _)

private theorem integral_growthSum :
    (∫ s in (0 : ℝ)..1, (8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
        4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) =
      (8 + Real.sqrt 3) * 4 + 4 * Real.sqrt 3 * (4 / 3) + 3 * (4 / 5) := by
  have h1 : IntervalIntegrable (fun s : ℝ => (8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ))
      volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(3 / 4))).const_mul _
  have h2 : IntervalIntegrable (fun s : ℝ => 4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ))
      volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(1 / 4))).const_mul _
  have h3 : IntervalIntegrable (fun s : ℝ => 3 * s ^ ((1 / 4) : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < (1 / 4))).const_mul _
  rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_rpow_neg_three_quarters,
    integral_rpow_neg_one_quarter, integral_rpow_one_quarter]

private theorem integral_growthTail {LM : ℝ} :
    (∫ s in (0 : ℝ)..1, Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)) =
      Real.sqrt 3 * 4 * Real.sqrt (LM + 1) := by
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    integral_rpow_neg_three_quarters]

private theorem integral_growthIntegrand_dimThree {Lm LM : ℝ} :
    (∫ s in (0 : ℝ)..1,
        ((8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) + 4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) +
            3 * s ^ ((1 / 4) : ℝ)) * Real.sqrt (Lm + 1) +
          Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)) =
      growthMajor * Real.sqrt (Lm + 1) + growthMinor * Real.sqrt (LM + 1) := by
  have htail : IntervalIntegrable
      (fun s : ℝ => Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)) volume 0 1 :=
    ((intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(3 / 4))).const_mul _).mul_const _
  rw [intervalIntegral.integral_add (intervalIntegrable_growthSum.mul_const _) htail,
    intervalIntegral.integral_mul_const, integral_growthTail, integral_growthSum]
  simp only [growthMajor, growthMinor]

private theorem growthMajor_sq_add_growthMinor_sq_le :
    growthMajor ^ 2 + growthMinor ^ 2 ≤ 4608 := by
  have h3lt : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h3nn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hmajor_lt : growthMajor < 54 := by
    dsimp only [growthMajor]
    nlinarith [h3lt, h3nn]
  have hmajor_nn : 0 ≤ growthMajor := by
    dsimp only [growthMajor]
    nlinarith [h3nn]
  have hminor_lt : growthMinor < 7 := by
    dsimp only [growthMinor]
    have h : Real.sqrt 3 < 7 / 4 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7 / 4)]
      norm_num
    nlinarith [h, h3nn]
  have hminor_nn : 0 ≤ growthMinor := by
    dsimp only [growthMinor]
    nlinarith [h3nn]
  nlinarith [hmajor_lt, hmajor_nn, hminor_lt, hminor_nn]

private theorem sq_le_of_growthBound {D Lm LM : ℝ} (hD : 0 ≤ D) (hLm : 0 ≤ Lm)
    (hLM : 0 ≤ LM)
    (h : D ≤ growthMajor * Real.sqrt (Lm + 1) + growthMinor * Real.sqrt (LM + 1)) :
    D ^ 2 ≤ 9216 * (LM + 1 + Lm) := by
  have hmajor : 0 ≤ growthMajor := by
    dsimp only [growthMajor]
    nlinarith [Real.sqrt_nonneg 3]
  have hminor : 0 ≤ growthMinor := by
    dsimp only [growthMinor]
    nlinarith [Real.sqrt_nonneg 3]
  have hnonneg : 0 ≤ growthMajor * Real.sqrt (Lm + 1) + growthMinor * Real.sqrt (LM + 1) :=
    add_nonneg (mul_nonneg hmajor (Real.sqrt_nonneg _))
      (mul_nonneg hminor (Real.sqrt_nonneg _))
  have hsqLm : (Real.sqrt (Lm + 1)) ^ 2 = Lm + 1 := Real.sq_sqrt (by linarith)
  have hsqLM : (Real.sqrt (LM + 1)) ^ 2 = LM + 1 := Real.sq_sqrt (by linarith)
  have hcs : (growthMajor * Real.sqrt (Lm + 1) + growthMinor * Real.sqrt (LM + 1)) ^ 2 ≤
      (growthMajor ^ 2 + growthMinor ^ 2) * (LM + Lm + 2) := by
    nlinarith [sq_nonneg (growthMajor * Real.sqrt (LM + 1) -
      growthMinor * Real.sqrt (Lm + 1)), hsqLm, hsqLM]
  have hsq : D ^ 2 ≤
      (growthMajor * Real.sqrt (Lm + 1) + growthMinor * Real.sqrt (LM + 1)) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hnonneg, abs_of_nonneg hD]
    exact h
  have ht : 0 ≤ LM + Lm := by linarith
  have hlast : (growthMajor ^ 2 + growthMinor ^ 2) * (LM + Lm + 2) ≤
      9216 * (LM + 1 + Lm) := by
    have h1 : (growthMajor ^ 2 + growthMinor ^ 2) * (LM + Lm) ≤
        4608 * (LM + Lm) :=
      mul_le_mul_of_nonneg_right growthMajor_sq_add_growthMinor_sq_le ht
    have h2 : (4608 : ℝ) * (LM + Lm) ≤ 9216 * (LM + Lm) := by nlinarith [ht]
    have h3 : (growthMajor ^ 2 + growthMinor ^ 2) * 2 ≤ 9216 := by
      nlinarith [growthMajor_sq_add_growthMinor_sq_le]
    nlinarith [h1, h2, h3]
  exact hsq.trans (hcs.trans hlast)

theorem right_pos_of_far_of_sq_le {D Lm LM : ℝ}
    (hfar : 1 + Lm < collapsedVolumeChi * D ^ 2)
    (hbound : D ^ 2 ≤ 9216 * (LM + 1 + Lm)) : 0 < LM := by
  have hchi : 0 < collapsedVolumeChi := collapsedVolumeChi_pos
  have hchiSq : collapsedVolumeChi * (9216 : ℝ) = 1 := by norm_num [collapsedVolumeChi]
  have h1 : collapsedVolumeChi * D ^ 2 ≤ collapsedVolumeChi * (9216 * (LM + 1 + Lm)) :=
    mul_le_mul_of_nonneg_left hbound hchi.le
  rw [← mul_assoc, hchiSq, one_mul] at h1
  linarith

theorem exists_far_sq_le_data :
    ∃ D Lm LM : ℝ, 0 ≤ D ∧ 0 ≤ Lm ∧ 0 ≤ LM ∧
      1 + Lm < collapsedVolumeChi * D ^ 2 ∧ D ^ 2 ≤ 9216 * (LM + 1 + Lm) ∧ 0 < LM := by
  refine ⟨100, 0, 399, by norm_num, le_rfl, by norm_num, ?_, by norm_num, by norm_num⟩
  norm_num [collapsedVolumeChi]

theorem eikonal_bound_at_far_data :
    100 ≤ ((8 + Real.sqrt 3) * 4 + 4 * Real.sqrt 3 * (4 / 3) + 3 * (4 / 5)) * Real.sqrt (0 + 1) +
      (Real.sqrt 3 * 4) * Real.sqrt (399 + 1) := by
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h400 : Real.sqrt (399 + 1) = 20 := by
    rw [show (399 : ℝ) + 1 = 20 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h400]
  nlinarith [h3]

theorem exists_far_not_sq_le :
    ∃ D Lm LM : ℝ, 0 ≤ D ∧ 0 ≤ Lm ∧ 0 ≤ LM ∧
      1 + Lm < collapsedVolumeChi * D ^ 2 ∧ ¬ D ^ 2 ≤ 9216 * (LM + 1 + Lm) := by
  refine ⟨1000, 0, 0, by norm_num, le_rfl, le_rfl, ?_, ?_⟩
  · norm_num [collapsedVolumeChi]
  · norm_num

end Numeric

section DistanceGrowth

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance boundTopology : TopologicalSpace F.M := F.topology
local instance boundCharted : ChartedSpace H F.M := F.charted
local instance boundSmooth : IsManifold I ∞ F.M := F.smooth
local instance boundT2 : T2Space F.M := F.t2
local instance boundSigma : SigmaCompactSpace F.M := F.sigmaCompact

def ReducedCostDistanceEikonal
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x a b : F.M) {tau : ℝ}, 0 < tau →
      redLength F.S 0 x b tau ≤ redLength F.S 0 x a tau →
      1 + redLength F.S 0 x b tau <
          collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau →
        (Real.sqrt tau)⁻¹ *
            (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal ≤
          ∫ s in (0 : ℝ)..1,
            ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) *
                s ^ (-(3 / 4) : ℝ) + 4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) +
              3 * s ^ ((1 / 4) : ℝ)) *
              Real.sqrt (redLength F.S 0 x b tau + 1) +
            Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) *
              Real.sqrt (redLength F.S 0 x a tau + 1)

def ReducedCostDistanceBound
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x a b : F.M) {tau : ℝ}, 0 < tau →
      redLength F.S 0 x b tau ≤ redLength F.S 0 x a tau →
      1 + redLength F.S 0 x b tau <
          collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau →
        ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 ≤
          9216 * tau * (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau)

def ReducedCostAdditiveBound
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x a b : F.M) {tau : ℝ}, 0 < tau →
      collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau - 1 ≤
        lCost F.S 0 x a tau / (2 * Real.sqrt tau) +
          lCost F.S 0 x b tau / (2 * Real.sqrt tau)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem intervalIntegrable_growthIntegrand {Lm LM : ℝ} :
    IntervalIntegrable (fun s : ℝ =>
      ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
        4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) *
        Real.sqrt (Lm + 1) +
      Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) * Real.sqrt (LM + 1)) volume 0 1 := by
  have h1 : IntervalIntegrable
      (fun s : ℝ => s ^ (-(3 / 4) : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(3 / 4))
  have h2 : IntervalIntegrable
      (fun s : ℝ => s ^ (-(1 / 4) : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 4))
  have h3 : IntervalIntegrable
      (fun s : ℝ => s ^ ((1 / 4) : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < (1 / 4))
  have hsum : IntervalIntegrable (fun s : ℝ =>
      (4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
        4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) volume 0 1 :=
    ((h1.const_mul _).add (h2.const_mul _)).add (h3.const_mul _)
  exact (hsum.mul_const _).add ((h1.const_mul (Real.sqrt 3)).mul_const _)

theorem reducedCostDistanceEikonal_of_distanceGrowth
    (h : ReducedCostDistanceGrowth (I := I) F) :
    ReducedCostDistanceEikonal (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau hle hfar
  obtain ⟨gamma₁, gamma₂, speed, h0₁, h0₂, h1₁, h1₂, hcont, hderiv, hint, hbound⟩ :=
    h hF hdim x a b htau hle hfar
  let U : ℝ → ℝ := fun s => (Real.sqrt tau)⁻¹ *
    (riemannianEDistOf (F.S.base.metric (-(tau * s))) (gamma₁ s) (gamma₂ s)).toReal
  have hftc : (∫ s in (0 : ℝ)..1, speed s) = U 1 - U 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint
  have hU0 : U 0 = 0 := by
    dsimp only [U]
    rw [mul_zero, neg_zero, h0₁, h0₂, riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
  have hU1 : U 1 = (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal := by
    dsimp only [U]
    rw [mul_one, h1₁, h1₂]
  have hnormsq : U 1 ≤ ∫ s in (0 : ℝ)..1, |speed s| := by
    have hval : U 1 = ∫ s in (0 : ℝ)..1, speed s := by rw [hftc, hU0, sub_zero]
    rw [hval]
    calc (∫ s in (0 : ℝ)..1, speed s) ≤ |∫ s in (0 : ℝ)..1, speed s| := le_abs_self _
      _ ≤ ∫ s in (0 : ℝ)..1, |speed s| :=
          intervalIntegral.norm_integral_le_integral_norm (μ := volume)
            (f := speed) (a := 0) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)
  have hmono : (∫ s in (0 : ℝ)..1, |speed s|) ≤
      ∫ s in (0 : ℝ)..1,
        ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
          4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) *
          Real.sqrt (redLength F.S 0 x b tau + 1) +
        Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) *
          Real.sqrt (redLength F.S 0 x a tau + 1) :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := 0) (b := 1)
      (by norm_num) hint.abs intervalIntegrable_growthIntegrand
      (fun s hs => hbound s ⟨hs.1, hs.2.le⟩)
  simpa only [hU1] using hnormsq.trans hmono

private theorem scalar_nonneg_of_ancient {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} :
    ∀ s ∈ Icc 0 tau, ∀ y : F.M, 0 ≤ F.S.scalar (0 - s) y := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  intro s hs y
  have hmem : -s ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr (by linarith [hs.1])
  simpa only [zero_sub] using (hC (-s) hmem y).1

private theorem redLength_nonneg_of_ancient {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    0 ≤ redLength F.S 0 x y tau := by
  rw [redLength]
  exact div_nonneg
    (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le (scalar_nonneg_of_ancient (I := I) F hF) x y)
    (by positivity)

private theorem self_le_of_near_regime {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) {c : ℝ}
    (hnear : c * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau ≤
      1 + lCost F.S 0 p p tau / (2 * Real.sqrt tau)) :
    c * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
        lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
      lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hother : 0 ≤ lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
    div_nonneg
      (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le
        (scalar_nonneg_of_ancient (I := I) F hF) p q)
      (by positivity)
  linarith

theorem reducedCostDistanceBound_of_eikonal
    (h : ReducedCostDistanceEikonal (I := I) F) : ReducedCostDistanceBound (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau hle hfar
  have hD := h hF hdim x a b htau hle hfar
  have hcoef : (4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) =
      8 + Real.sqrt 3 := by
    simp only [hdim]
    norm_num
  have hEq : (∫ s in (0 : ℝ)..1,
        ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
          4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) *
          Real.sqrt (redLength F.S 0 x b tau + 1) +
        Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) *
          Real.sqrt (redLength F.S 0 x a tau + 1)) =
      growthMajor * Real.sqrt (redLength F.S 0 x b tau + 1) +
        growthMinor * Real.sqrt (redLength F.S 0 x a tau + 1) := by
    rw [show (∫ s in (0 : ℝ)..1,
          ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) +
            4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) + 3 * s ^ ((1 / 4) : ℝ)) *
            Real.sqrt (redLength F.S 0 x b tau + 1) +
          Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) *
            Real.sqrt (redLength F.S 0 x a tau + 1)) =
        (∫ s in (0 : ℝ)..1,
          ((8 + Real.sqrt 3) * s ^ (-(3 / 4) : ℝ) + 4 * Real.sqrt 3 * s ^ (-(1 / 4) : ℝ) +
              3 * s ^ ((1 / 4) : ℝ)) * Real.sqrt (redLength F.S 0 x b tau + 1) +
            Real.sqrt 3 * s ^ (-(3 / 4) : ℝ) *
              Real.sqrt (redLength F.S 0 x a tau + 1)) from
      intervalIntegral.integral_congr (fun s _ => by rw [hcoef])]
    exact integral_growthIntegrand_dimThree
  have hbound : (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal ≤
      growthMajor * Real.sqrt (redLength F.S 0 x b tau + 1) +
        growthMinor * Real.sqrt (redLength F.S 0 x a tau + 1) := hD.trans_eq hEq
  have hDnn : 0 ≤ (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal :=
    mul_nonneg (by positivity) (by positivity)
  have hsq := sq_le_of_growthBound hDnn
    (redLength_nonneg_of_ancient (I := I) F hF x b htau)
    (redLength_nonneg_of_ancient (I := I) F hF x a htau) hbound
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
        mul_le_mul_of_nonneg_left hsq htau.le
    _ = 9216 * tau * (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau) := by ring

theorem reducedCostDistanceBound_of_additive
    (h : ReducedCostAdditiveBound (I := I) F) : ReducedCostDistanceBound (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau hle hfar
  have hkey := h hF hdim x a b htau
  have hchiSq : collapsedVolumeChi * (9216 : ℝ) = 1 := by norm_num [collapsedVolumeChi]
  change ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 ≤
    9216 * tau * (lCost F.S 0 x a tau / (2 * Real.sqrt tau) + 1 +
      lCost F.S 0 x b tau / (2 * Real.sqrt tau))
  have hkey' : collapsedVolumeChi *
      ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 ≤
      (lCost F.S 0 x a tau / (2 * Real.sqrt tau) + 1 +
        lCost F.S 0 x b tau / (2 * Real.sqrt tau)) * tau := by
    have h0 : collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau ≤
        lCost F.S 0 x a tau / (2 * Real.sqrt tau) + 1 +
          lCost F.S 0 x b tau / (2 * Real.sqrt tau) := by linarith
    rwa [div_le_iff₀ htau] at h0
  have hX : ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 =
      collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 *
        9216 := by
    rw [mul_assoc, mul_comm (((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2)
      (9216 : ℝ), ← mul_assoc, hchiSq, one_mul]
  calc
    ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 =
        collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 *
          9216 := hX
    _ ≤ ((lCost F.S 0 x a tau / (2 * Real.sqrt tau) + 1 +
          lCost F.S 0 x b tau / (2 * Real.sqrt tau)) * tau) * 9216 :=
        mul_le_mul_of_nonneg_right hkey' (by norm_num)
    _ = 9216 * tau * (lCost F.S 0 x a tau / (2 * Real.sqrt tau) + 1 +
          lCost F.S 0 x b tau / (2 * Real.sqrt tau)) := by ring

theorem ancientKappaThree_reducedCost_two_point_of_additive
    (hbound : ReducedCostAdditiveBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hkey := hbound hF hdim p p q htau
  linarith

theorem ancientKappaThree_reducedCost_two_point_of_distanceBound
    (hbound : ReducedCostDistanceBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hdist : (riemannianEDistOf (F.S.base.metric (-tau)) q p).toReal =
      (riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal := by
    rw [riemannianEDistOf_comm]
  have hchi : collapsedVolumeChi = (9216 : ℝ)⁻¹ := by norm_num [collapsedVolumeChi]
  rcases le_total (redLength F.S 0 p q tau) (redLength F.S 0 p p tau) with hle | hle
  · by_cases hfar : 1 + redLength F.S 0 p p tau < collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau
    · have hfar' : 1 + redLength F.S 0 p q tau < collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau := by linarith
      have hdata := hbound hF hdim p p q htau hle hfar'
      have hkey : collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau ≤
          redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau := by
        rw [hchi, div_le_iff₀ htau]
        calc
          (9216 : ℝ)⁻¹ * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 ≤
              (9216 : ℝ)⁻¹ * (9216 * tau *
                (redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau)) :=
            mul_le_mul_of_nonneg_left hdata (by norm_num)
          _ = (redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau) * tau := by
            field_simp
      have hmain : collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
          redLength F.S 0 p p tau ≤ redLength F.S 0 p q tau := by linarith [hkey]
      simpa only [redLength] using hmain
    · exact self_le_of_near_regime (I := I) F hF p q htau (le_of_not_gt hfar)
  · by_cases hfar : 1 + redLength F.S 0 p p tau < collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau
    · have hfar' : 1 + redLength F.S 0 p p tau < collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) q p).toReal) ^ 2 / tau := by
        rw [hdist]
        exact hfar
      have hdata := hbound hF hdim p q p htau hle hfar'
      rw [hdist] at hdata
      have hkey : collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau ≤
          redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau := by
        rw [hchi, div_le_iff₀ htau]
        calc
          (9216 : ℝ)⁻¹ * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 ≤
              (9216 : ℝ)⁻¹ * (9216 * tau *
                (redLength F.S 0 p q tau + 1 + redLength F.S 0 p p tau)) :=
            mul_le_mul_of_nonneg_left hdata (by norm_num)
          _ = (redLength F.S 0 p p tau + 1 + redLength F.S 0 p q tau) * tau := by
            ring
      have hmain : collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
          redLength F.S 0 p p tau ≤ redLength F.S 0 p q tau := by linarith [hkey]
      simpa only [redLength] using hmain
    · exact self_le_of_near_regime (I := I) F hF p q htau (le_of_not_gt hfar)

end DistanceGrowth

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
