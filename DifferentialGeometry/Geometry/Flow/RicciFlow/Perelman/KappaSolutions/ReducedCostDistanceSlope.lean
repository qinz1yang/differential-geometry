import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostDistanceBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set MeasureTheory intervalIntegral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance distanceSlopeTopology : TopologicalSpace F.M := F.topology
local instance distanceSlopeCharted : ChartedSpace H F.M := F.charted
local instance distanceSlopeSmooth : IsManifold I ∞ F.M := F.smooth
local instance distanceSlopeT2 : T2Space F.M := F.t2
local instance distanceSlopeSigma : SigmaCompactSpace F.M := F.sigmaCompact

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem intervalIntegrable_reducedCostSlopeIntegrand {Lm LM : ℝ} :
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

private theorem redLength_nonneg_of_ancient_data {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (x y : F.M) {tau : ℝ} (htau : 0 < tau) :
    0 ≤ redLength F.S 0 x y tau := by
  rw [redLength]
  refine div_nonneg (lCost_nonneg_of_scalar_nonneg F.S 0 htau.le ?_ x y) (by positivity)
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  intro s hs y'
  have hmem : -s ∈ ancientTimeInterval.carrier := by
    rw [ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr (by linarith [hs.1])
  simpa only [zero_sub] using (hC (-s) hmem y').1

def ReducedCostDistanceSlope
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x a b : F.M) {tau : ℝ}, 0 < tau →
      redLength F.S 0 x b tau ≤ redLength F.S 0 x a tau →
      1 + redLength F.S 0 x b tau <
          collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau →
        ∃ (gamma₁ gamma₂ : ℝ → F.M),
          gamma₁ 0 = x ∧ gamma₂ 0 = x ∧ gamma₁ 1 = a ∧ gamma₂ 1 = b ∧
          ContinuousOn (fun s : ℝ => (Real.sqrt tau)⁻¹ *
            (riemannianEDistOf (F.S.base.metric (-(tau * s))) (gamma₁ s) (gamma₂ s)).toReal)
            (Icc 0 1) ∧
          (∀ c ∈ Ioc (0 : ℝ) 1, AbsolutelyContinuousOnInterval
            (fun s : ℝ => (Real.sqrt tau)⁻¹ *
              (riemannianEDistOf (F.S.base.metric (-(tau * s)))
                (gamma₁ s) (gamma₂ s)).toReal) c 1) ∧
          ∀ t ∈ Ioo (0 : ℝ) 1, ∀ eps : ℝ, 0 < eps →
            ∀ᶠ s in 𝓝[>] t,
              slope (fun r : ℝ => (Real.sqrt tau)⁻¹ *
                (riemannianEDistOf (F.S.base.metric (-(tau * r)))
                  (gamma₁ r) (gamma₂ r)).toReal) t s ≤
                ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) *
                    t ^ (-(3 / 4) : ℝ) +
                  4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) + 3 * t ^ ((1 / 4) : ℝ)) *
                  Real.sqrt (redLength F.S 0 x b tau + 1) +
                Real.sqrt 3 * t ^ (-(3 / 4) : ℝ) *
                  Real.sqrt (redLength F.S 0 x a tau + 1) + eps

theorem reducedCostDistanceEikonal_of_slope
    (h : ReducedCostDistanceSlope (I := I) F) : ReducedCostDistanceEikonal (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau hle hfar
  obtain ⟨gamma₁, gamma₂, h0₁, h0₂, h1₁, h1₂, hcont, hac, hdini⟩ :=
    h hF hdim x a b htau hle hfar
  let U : ℝ → ℝ := fun s => (Real.sqrt tau)⁻¹ *
    (riemannianEDistOf (F.S.base.metric (-(tau * s))) (gamma₁ s) (gamma₂ s)).toReal
  let G : ℝ → ℝ := fun t =>
    ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) +
      4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) + 3 * t ^ ((1 / 4) : ℝ)) *
      Real.sqrt (redLength F.S 0 x b tau + 1) +
    Real.sqrt 3 * t ^ (-(3 / 4) : ℝ) * Real.sqrt (redLength F.S 0 x a tau + 1)
  have hGint : IntervalIntegrable G volume 0 1 :=
    intervalIntegrable_reducedCostSlopeIntegrand (E := E)
      (Lm := redLength F.S 0 x b tau) (LM := redLength F.S 0 x a tau)
  have hcontU : ContinuousOn U (Icc 0 1) := hcont
  have hacU : ∀ c ∈ Ioc (0 : ℝ) 1, AbsolutelyContinuousOnInterval U c 1 := hac
  have hdiniU : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ eps : ℝ, 0 < eps →
      ∀ᶠ s in 𝓝[>] t, slope U t s ≤ G t + eps := hdini
  have hstep := ContinuousOn.sub_le_integral_of_dini_le (f := U) (g := G) (a := 0) (b := 1)
    (by norm_num) hcontU hacU hGint hdiniU
  have hU0 : U 0 = 0 := by
    dsimp only [U]
    rw [mul_zero, neg_zero, h0₁, h0₂, riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
  have hU1 : U 1 = (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal := by
    dsimp only [U]
    rw [mul_one, h1₁, h1₂]
  have hmain : (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal ≤ ∫ s in (0 : ℝ)..1, G s := by
    have h' : U 1 - U 0 ≤ ∫ s in (0 : ℝ)..1, G s := hstep
    rwa [hU1, hU0, sub_zero] at h'
  simpa only [G] using hmain

theorem reducedCostDistanceBound_of_slope
    (h : ReducedCostDistanceSlope (I := I) F) : ReducedCostDistanceBound (I := I) F :=
  reducedCostDistanceBound_of_eikonal (I := I) F (reducedCostDistanceEikonal_of_slope (I := I) F h)

theorem ancientKappaThree_reducedCost_two_point_of_slope
    (h : ReducedCostDistanceSlope (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
  ancientKappaThree_reducedCost_two_point_of_distanceBound (I := I) F
    (reducedCostDistanceBound_of_slope (I := I) F h) hF hdim p q htau

theorem reducedCostDistanceSlope_of_growth
    (h : ReducedCostDistanceGrowth (I := I) F) : ReducedCostDistanceSlope (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau hle hfar
  obtain ⟨gamma₁, gamma₂, speed, h0₁, h0₂, h1₁, h1₂, hcont, hderiv, hint, hbound⟩ :=
    h hF hdim x a b htau hle hfar
  let U : ℝ → ℝ := fun s => (Real.sqrt tau)⁻¹ *
    (riemannianEDistOf (F.S.base.metric (-(tau * s))) (gamma₁ s) (gamma₂ s)).toReal
  let G : ℝ → ℝ := fun t =>
    ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) +
      4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) + 3 * t ^ ((1 / 4) : ℝ)) *
      Real.sqrt (redLength F.S 0 x b tau + 1) +
    Real.sqrt 3 * t ^ (-(3 / 4) : ℝ) * Real.sqrt (redLength F.S 0 x a tau + 1)
  have hderivU : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt U (speed t) t := hderiv
  have hboundU : ∀ t ∈ Ioc (0 : ℝ) 1, |speed t| ≤ G t := hbound
  have hcontU : ContinuousOn U (Icc 0 1) := hcont
  have hIntU : ∀ c ∈ Ioc (0 : ℝ) 1, IntervalIntegrable speed volume c 1 := by
    intro c hc
    refine hint.mono_set (fun y hy => ?_)
    rw [uIcc_of_le hc.2] at hy
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hc.1.le.trans hy.1, hy.2⟩
  have hftcU : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Icc c 1,
      (∫ r in c..y, speed r) = U y - U c := by
    intro c hc y hy
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy.1 ?_ ?_ ?_
    · exact hcontU.mono (Icc_subset_Icc hc.1.le hy.2)
    · intro r hr
      exact hderivU r ⟨hc.1.trans hr.1, hr.2.trans_le hy.2⟩
    · refine hint.mono_set ?_
      intro r hr
      rw [uIcc_of_le hy.1] at hr
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨hc.1.le.trans hr.1, le_trans hr.2 hy.2⟩
  refine ⟨gamma₁, gamma₂, h0₁, h0₂, h1₁, h1₂, hcontU, ?_, ?_⟩
  · intro c hc
    have hAcInt : AbsolutelyContinuousOnInterval (fun y => ∫ r in c..y, speed r) c 1 :=
      (hIntU c hc).absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
    have hAcConst : AbsolutelyContinuousOnInterval (fun _ : ℝ => U c) c 1 :=
      (LipschitzWith.const (U c)).lipschitzOnWith.absolutelyContinuousOnInterval
    refine (hAcConst.add hAcInt).congr ?_
    intro y hy
    rw [uIcc_of_le hc.2] at hy
    simp only [Pi.add_apply]
    linarith [hftcU c hc y hy]
  · intro t ht eps heps
    have hspeed : speed t ≤ G t := (abs_le.mp (hboundU t ⟨ht.1, ht.2.le⟩)).2
    filter_upwards [((hderivU t ht).tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)).eventually_lt_const
      (by linarith : speed t < G t + eps)] with s hs
    exact le_of_lt hs

theorem reducedCostAdditiveBound_of_distanceBound
    (h : ReducedCostDistanceBound (I := I) F) : ReducedCostAdditiveBound (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau
  have hchi : collapsedVolumeChi = (9216 : ℝ)⁻¹ := by norm_num [collapsedVolumeChi]
  have hsym : (riemannianEDistOf (F.S.base.metric (-tau)) b a).toReal =
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal := by
    rw [riemannianEDistOf_comm]
  have hnonneg_b := redLength_nonneg_of_ancient_data F hF x b htau
  have hkey : collapsedVolumeChi *
      ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau ≤
      redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau := by
    rcases le_total (redLength F.S 0 x b tau) (redLength F.S 0 x a tau) with hle | hle
    · by_cases hfar : 1 + redLength F.S 0 x b tau < collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau
      · have hdata := h hF hdim x a b htau hle hfar
        rw [hchi, div_le_iff₀ htau]
        calc (9216 : ℝ)⁻¹ *
              ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 ≤
              (9216 : ℝ)⁻¹ * (9216 * tau *
                (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau)) :=
              mul_le_mul_of_nonneg_left hdata (by norm_num)
          _ = (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau) * tau := by
              field_simp
      · linarith [le_of_not_gt hfar]
    · by_cases hfar : 1 + redLength F.S 0 x a tau < collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau
      · have hfar' : 1 + redLength F.S 0 x a tau < collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) b a).toReal) ^ 2 / tau := by
          rw [hsym]
          exact hfar
        have hdata := h hF hdim x b a htau hle hfar'
        rw [hsym] at hdata
        rw [hchi, div_le_iff₀ htau]
        calc (9216 : ℝ)⁻¹ *
              ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 ≤
              (9216 : ℝ)⁻¹ * (9216 * tau *
                (redLength F.S 0 x b tau + 1 + redLength F.S 0 x a tau)) :=
              mul_le_mul_of_nonneg_left hdata (by norm_num)
          _ = (redLength F.S 0 x a tau + 1 + redLength F.S 0 x b tau) * tau := by
              field_simp
              ring
      · linarith [le_of_not_gt hfar, hnonneg_b]
  calc collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau - 1 ≤
        redLength F.S 0 x a tau + redLength F.S 0 x b tau := by linarith [hkey]
    _ = lCost F.S 0 x a tau / (2 * Real.sqrt tau) +
        lCost F.S 0 x b tau / (2 * Real.sqrt tau) := by
        rw [redLength, redLength]

theorem reducedCostDistanceBound_iff_reducedCostAdditiveBound :
    ReducedCostDistanceBound (I := I) F ↔ ReducedCostAdditiveBound (I := I) F :=
  ⟨reducedCostAdditiveBound_of_distanceBound (I := I) F,
    reducedCostDistanceBound_of_additive (I := I) F⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
