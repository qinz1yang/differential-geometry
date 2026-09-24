import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostDistanceSlope
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostPoleBound


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance reducedCostTwoPointReductionTopology : TopologicalSpace F.M := F.topology
local instance reducedCostTwoPointReductionCharted : ChartedSpace H F.M := F.charted
local instance reducedCostTwoPointReductionSmooth : IsManifold I ∞ F.M := F.smooth
local instance reducedCostTwoPointReductionT2 : T2Space F.M := F.t2
local instance reducedCostTwoPointReductionSigma : SigmaCompactSpace F.M := F.sigmaCompact

def ReducedCostPoleFarBound
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x b : F.M) {tau : ℝ}, 0 < tau →
      1 + redLength F.S 0 x x tau <
          collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) x b).toReal) ^ 2 / tau →
        collapsedVolumeChi *
            ((riemannianEDistOf (F.S.base.metric (-tau)) x b).toReal) ^ 2 / tau - 1 ≤
          lCost F.S 0 x x tau / (2 * Real.sqrt tau) +
            lCost F.S 0 x b tau / (2 * Real.sqrt tau)

omit [I.Boundaryless] in
theorem reducedCostPoleFarBound_of_poleBound
    (h : ReducedCostPoleBound (I := I) F) : ReducedCostPoleFarBound (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x b tau htau _
  exact h hF hdim x b htau

omit [I.Boundaryless] in
theorem reducedCostPoleBound_of_poleFarBound
    (h : ReducedCostPoleFarBound (I := I) F) : ReducedCostPoleBound (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x b tau htau
  by_cases hfar : 1 + redLength F.S 0 x x tau <
      collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) x b).toReal) ^ 2 / tau
  · exact h hF hdim x b htau hfar
  · have hnear := reducedCost_two_point_of_near_regime (I := I) F hF x b htau
      (c := collapsedVolumeChi) ?_
    · linarith
    · simpa only [redLength] using le_of_not_gt hfar

omit [I.Boundaryless] in
theorem reducedCostPoleBound_iff_poleFarBound :
    ReducedCostPoleBound (I := I) F ↔ ReducedCostPoleFarBound (I := I) F :=
  ⟨reducedCostPoleFarBound_of_poleBound (I := I) F,
    reducedCostPoleBound_of_poleFarBound (I := I) F⟩

omit [I.Boundaryless] in
theorem ancientKappaThree_reducedCost_two_point_of_poleFarBound
    (h : ReducedCostPoleFarBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
  ancientKappaThree_reducedCost_two_point_of_poleBound (I := I) F
    (reducedCostPoleBound_of_poleFarBound (I := I) F h) hF hdim p q htau

omit [I.Boundaryless] in
theorem ancientKappaThree_reducedCost_two_point_of_not_far
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau)
    (hnear : ¬ 1 + redLength F.S 0 p p tau <
      collapsedVolumeChi * ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  refine reducedCost_two_point_of_near_regime (I := I) F hF p q htau
    (c := collapsedVolumeChi) ?_
  simpa only [redLength] using le_of_not_gt hnear

omit [I.Boundaryless] in
theorem reducedCostPoleFarBound_of_additiveBound
    (h : ReducedCostAdditiveBound (I := I) F) : ReducedCostPoleFarBound (I := I) F :=
  reducedCostPoleFarBound_of_poleBound (I := I) F
    (reducedCostPoleBound_of_additiveBound (I := I) F h)

omit [I.Boundaryless] in
theorem reducedCostPoleFarBound_of_distanceBound
    (h : ReducedCostDistanceBound (I := I) F) : ReducedCostPoleFarBound (I := I) F :=
  reducedCostPoleFarBound_of_additiveBound (I := I) F
    (reducedCostAdditiveBound_of_distanceBound (I := I) F h)

omit [I.Boundaryless] in
theorem reducedCostPoleFarBound_of_distanceSlope
    (h : ReducedCostDistanceSlope (I := I) F) : ReducedCostPoleFarBound (I := I) F :=
  reducedCostPoleFarBound_of_distanceBound (I := I) F
    (reducedCostDistanceBound_of_slope (I := I) F h)

omit [I.Boundaryless] in
theorem reducedCostPoleFarBound_of_distanceGrowth
    (h : ReducedCostDistanceGrowth (I := I) F) : ReducedCostPoleFarBound (I := I) F :=
  reducedCostPoleFarBound_of_distanceSlope (I := I) F
    (reducedCostDistanceSlope_of_growth (I := I) F h)

theorem exists_far_pole_data :
    ∃ D Lm LM : ℝ, 0 ≤ D ∧ 0 ≤ Lm ∧ 0 ≤ LM ∧
      1 + Lm < collapsedVolumeChi * D ^ 2 ∧
      collapsedVolumeChi * D ^ 2 - 1 = Lm + LM ∧ 0 < LM := by
  refine ⟨288, 3, 5, by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num⟩
  · norm_num [collapsedVolumeChi]
  · norm_num [collapsedVolumeChi]

theorem exists_far_pole_data_not_near :
    ∃ D Lm : ℝ, 0 ≤ D ∧ 0 ≤ Lm ∧ 1 + Lm < collapsedVolumeChi * D ^ 2 ∧
      ¬ collapsedVolumeChi * D ^ 2 ≤ 1 + Lm := by
  refine ⟨288, 3, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [collapsedVolumeChi]
  · norm_num [collapsedVolumeChi]

theorem exists_far_pole_data_not_bound :
    ∃ D Lm : ℝ, 0 ≤ D ∧ 0 ≤ Lm ∧ 1 + Lm < collapsedVolumeChi * D ^ 2 ∧
      ¬ collapsedVolumeChi * D ^ 2 - 1 ≤ Lm := by
  refine ⟨1000, 0, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [collapsedVolumeChi]
  · norm_num [collapsedVolumeChi]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
