import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostDistanceBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostDistanceGrowth

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance reducedCostPoleBoundTopology : TopologicalSpace F.M := F.topology
local instance reducedCostPoleBoundCharted : ChartedSpace H F.M := F.charted
local instance reducedCostPoleBoundSmooth : IsManifold I ∞ F.M := F.smooth
local instance reducedCostPoleBoundT2 : T2Space F.M := F.t2
local instance reducedCostPoleBoundSigma : SigmaCompactSpace F.M := F.sigmaCompact

def ReducedCostPoleBound
    (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval) : Prop :=
  ∀ {kappa : ℝ}, IsAncientKappaSolution kappa F → ∀ (hdim : Module.finrank ℝ E = 3),
    let _ := hdim
    ∀ (x b : F.M) {tau : ℝ}, 0 < tau →
      collapsedVolumeChi *
          ((riemannianEDistOf (F.S.base.metric (-tau)) x b).toReal) ^ 2 / tau - 1 ≤
        lCost F.S 0 x x tau / (2 * Real.sqrt tau) +
          lCost F.S 0 x b tau / (2 * Real.sqrt tau)

omit [I.Boundaryless] in
theorem reducedCostPoleBound_of_additiveBound
    (h : ReducedCostAdditiveBound (I := I) F) : ReducedCostPoleBound (I := I) F := by
  intro kappa hF hdim
  dsimp only
  intro x b tau htau
  have hkey := h hF hdim x x b htau
  linarith

omit [I.Boundaryless] in
theorem ancientKappaThree_reducedCost_two_point_of_poleBound
    (h : ReducedCostPoleBound (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  have hkey := h hF hdim p q htau
  linarith

omit [I.Boundaryless] in
theorem ancientKappaThree_reducedCost_two_point_of_growth
    (h : ReducedCostDistanceGrowth (I := I) F)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) :=
  ancientKappaThree_reducedCost_two_point_of_distanceGrowth (I := I) F h hF hdim p q htau

omit [I.Boundaryless] in
theorem reducedCost_poleBound_self {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (x : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) x x).toReal) ^ 2 / tau - 1 ≤
      lCost F.S 0 x x tau / (2 * Real.sqrt tau) +
        lCost F.S 0 x x tau / (2 * Real.sqrt tau) := by
  have hself : (riemannianEDistOf (F.S.base.metric (-tau)) x x).toReal = 0 := by
    rw [riemannianEDistOf_self, ENNReal.toReal_zero]
  have hscalar : ∀ s ∈ Icc 0 tau, ∀ y : F.M, 0 ≤ F.S.scalar (0 - s) y := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro s hs y
    have hmem : -s ∈ ancientTimeInterval.carrier := by
      rw [ancientTimeInterval_carrier]
      exact Set.mem_Iic.mpr (by linarith [hs.1])
    simpa only [zero_sub] using (hC (-s) hmem y).1
  have hnonneg : 0 ≤ lCost F.S 0 x x tau :=
    lCost_nonneg_of_scalar_nonneg F.S 0 htau.le hscalar x x
  have hquot : 0 ≤ lCost F.S 0 x x tau / (2 * Real.sqrt tau) :=
    div_nonneg hnonneg (by positivity)
  rw [hself]
  norm_num
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
