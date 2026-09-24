import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostDistanceSlope

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

local instance reducedCostChangingTopology : TopologicalSpace F.M := F.topology
local instance reducedCostChangingCharted : ChartedSpace H F.M := F.charted
local instance reducedCostChangingSmooth : IsManifold I ∞ F.M := F.smooth
local instance reducedCostChangingT2 : T2Space F.M := F.t2
local instance reducedCostChangingSigma : SigmaCompactSpace F.M := F.sigmaCompact

def ReducedCostChangingDistanceBound
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x a b : F.M) {tau : ℝ}, 0 < tau →
      redLength F.S 0 x b tau ≤ redLength F.S 0 x a tau →
      1 + redLength F.S 0 x b tau <
          collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal) ^ 2 / tau →
        ∃ D : ℝ → ℝ,
          D 0 = 0 ∧
          D 1 = (Real.sqrt tau)⁻¹ *
            (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal ∧
          ContinuousOn D (Icc 0 1) ∧
          (∀ c ∈ Ioc (0 : ℝ) 1, AbsolutelyContinuousOnInterval D c 1) ∧
          ∀ t ∈ Ioo (0 : ℝ) 1, ∀ eps : ℝ, 0 < eps →
            ∀ᶠ s in 𝓝[>] t,
              slope D t s ≤
                ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) *
                    t ^ (-(3 / 4) : ℝ) +
                  4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) + 3 * t ^ ((1 / 4) : ℝ)) *
                  Real.sqrt (redLength F.S 0 x b tau + 1) +
                Real.sqrt 3 * t ^ (-(3 / 4) : ℝ) *
                  Real.sqrt (redLength F.S 0 x a tau + 1) + eps

theorem collapsedVolumeChi_eq_blueprint_two_point_constant :
    collapsedVolumeChi = (576 * ((3 : ℝ) + 1) ^ 2)⁻¹ := by
  norm_num [collapsedVolumeChi]

theorem collapsedVolumeChi_mul_two_point_denominator :
    collapsedVolumeChi * 9216 = 1 := by
  norm_num [collapsedVolumeChi]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem intervalIntegrable_changingDistanceIntegrand {Lm LM : ℝ} :
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

theorem exists_endpoint_integral_data_not_dini_bound :
    ∃ D : ℝ → ℝ, ContinuousOn D (Icc (0 : ℝ) 1) ∧ D 0 = 0 ∧ D 1 = 1 ∧
      D 1 - D 0 ≤ ∫ _ in (0 : ℝ)..1, (1 : ℝ) ∧
      ¬ (∀ t ∈ Ioo (0 : ℝ) 1, ∀ eps : ℝ, 0 < eps →
        ∀ᶠ s in 𝓝[>] t, slope D t s ≤ (1 : ℝ) + eps) := by
  let D : ℝ → ℝ := fun t => max 0 (2 * (t - 1 / 2))
  have hD0 : D 0 = 0 := by
    dsimp only [D]
    norm_num
  have hD1 : D 1 = 1 := by
    dsimp only [D]
    norm_num
  have hcont : ContinuousOn D (Icc (0 : ℝ) 1) := by
    dsimp only [D]
    exact (continuous_const.max
      (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  refine ⟨D, hcont, hD0, hD1, ?_, ?_⟩
  · rw [hD1, hD0, sub_zero]
    simp
  · intro h
    have h1 := h (1 / 2) ⟨by norm_num, by norm_num⟩ (1 / 2) (by norm_num)
    have h2 : ∀ᶠ s in 𝓝[>] ((1 : ℝ) / 2), s ∈ Ioo ((1 : ℝ) / 2) (3 / 4) :=
      Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨s, hsl, hs⟩ := (h1.and h2).exists
    have hslt : (1 : ℝ) / 2 < s := hs.1
    have hDs : D s = 2 * (s - 1 / 2) := by
      dsimp only [D]
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 2 * (s - 1 / 2))]
    have hDt : D (1 / 2) = 0 := by
      dsimp only [D]
      norm_num
    have hslope : slope D (1 / 2) s = 2 := by
      rw [slope_def_field, hDs, hDt, sub_zero]
      have hne : s - 1 / 2 ≠ 0 := by linarith
      rw [div_eq_iff hne]
    rw [hslope] at hsl
    linarith

theorem reducedCostDistanceEikonal_of_changingDistance
    (h : ReducedCostChangingDistanceBound (I := I) F) :
    ReducedCostDistanceEikonal (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau hle hfar
  obtain ⟨D, hD0, hD1, hcont, hac, hdini⟩ := h hF hdim x a b htau hle hfar
  let G : ℝ → ℝ := fun t =>
    ((4 + 2 * ((Module.finrank ℝ E : ℝ) - 1) + Real.sqrt 3) * t ^ (-(3 / 4) : ℝ) +
      4 * Real.sqrt 3 * t ^ (-(1 / 4) : ℝ) + 3 * t ^ ((1 / 4) : ℝ)) *
      Real.sqrt (redLength F.S 0 x b tau + 1) +
    Real.sqrt 3 * t ^ (-(3 / 4) : ℝ) * Real.sqrt (redLength F.S 0 x a tau + 1)
  have hGint : IntervalIntegrable G volume 0 1 :=
    intervalIntegrable_changingDistanceIntegrand (E := E)
      (Lm := redLength F.S 0 x b tau) (LM := redLength F.S 0 x a tau)
  have hstep := ContinuousOn.sub_le_integral_of_dini_le (f := D) (g := G) (a := 0) (b := 1)
    (by norm_num) hcont hac hGint hdini
  have hmain : (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-tau)) a b).toReal ≤ ∫ s in (0 : ℝ)..1, G s := by
    have h' : D 1 - D 0 ≤ ∫ s in (0 : ℝ)..1, G s := hstep
    rwa [hD1, hD0, sub_zero] at h'
  simpa only [G] using hmain

theorem reducedCostDistanceBound_of_changingDistance
    (h : ReducedCostChangingDistanceBound (I := I) F) :
    ReducedCostDistanceBound (I := I) F :=
  reducedCostDistanceBound_of_eikonal (I := I) F
    (reducedCostDistanceEikonal_of_changingDistance (I := I) F h)

theorem ancientKappaThree_reducedCost_two_point_of_changingDistance
    (h : ReducedCostChangingDistanceBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
  ancientKappaThree_reducedCost_two_point_of_distanceBound (I := I) F
    (reducedCostDistanceBound_of_changingDistance (I := I) F h) hF hdim p q htau

theorem reducedCostChangingDistanceBound_of_slope
    (h : ReducedCostDistanceSlope (I := I) F) :
    ReducedCostChangingDistanceBound (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x a b tau htau hle hfar
  obtain ⟨gamma₁, gamma₂, h0₁, h0₂, h1₁, h1₂, hcont, hac, hdini⟩ :=
    h hF hdim x a b htau hle hfar
  refine ⟨fun s : ℝ => (Real.sqrt tau)⁻¹ *
      (riemannianEDistOf (F.S.base.metric (-(tau * s))) (gamma₁ s) (gamma₂ s)).toReal,
    ?_, ?_, hcont, hac, hdini⟩
  · dsimp only
    rw [mul_zero, neg_zero, h0₁, h0₂, riemannianEDistOf_self, ENNReal.toReal_zero, mul_zero]
  · dsimp only
    rw [mul_one, h1₁, h1₂]

theorem reducedCostChangingDistanceBound_of_growth
    (h : ReducedCostDistanceGrowth (I := I) F) :
    ReducedCostChangingDistanceBound (I := I) F :=
  reducedCostChangingDistanceBound_of_slope (I := I) F
    (reducedCostDistanceSlope_of_growth (I := I) F h)

theorem ancientKappaThree_reducedCost_two_point_of_slope_reduction
    (h : ReducedCostDistanceSlope (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
  ancientKappaThree_reducedCost_two_point_of_changingDistance (I := I) F
    (reducedCostChangingDistanceBound_of_slope (I := I) F h) hF hdim p q htau

theorem ancientKappaThree_reducedCost_two_point_self {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p p).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p p tau / (2 * Real.sqrt tau) := by
  refine reducedCost_two_point_of_near_regime (I := I) F hF p p htau
    (c := collapsedVolumeChi) ?_
  have hself : (riemannianEDistOf (F.S.base.metric (-tau)) p p).toReal = 0 := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero]
  rw [hself]
  have hscalar : ∀ s ∈ Icc 0 tau, ∀ y : F.M, 0 ≤ F.S.scalar (0 - s) y := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro s hs y
    have hmem : -s ∈ ancientTimeInterval.carrier := by
      rw [ancientTimeInterval_carrier]
      exact Set.mem_Iic.mpr (by linarith [hs.1])
    simpa only [zero_sub] using (hC (-s) hmem y).1
  have hnonneg : 0 ≤ lCost F.S 0 p p tau :=
    lCost_nonneg_of_scalar_nonneg F.S 0 htau.le hscalar p p
  have hquot : 0 ≤ lCost F.S 0 p p tau / (2 * Real.sqrt tau) :=
    div_nonneg hnonneg (by positivity)
  have hzero : collapsedVolumeChi * (0 : ℝ) ^ 2 / tau = 0 := by norm_num
  rw [hzero]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
