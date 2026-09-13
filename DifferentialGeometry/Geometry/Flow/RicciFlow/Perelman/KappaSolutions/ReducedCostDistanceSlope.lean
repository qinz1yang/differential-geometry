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
