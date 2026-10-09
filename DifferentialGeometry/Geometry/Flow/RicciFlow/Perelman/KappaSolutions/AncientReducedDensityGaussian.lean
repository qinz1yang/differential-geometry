import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalGaussianTopology : TopologicalSpace F.M := F.topology
local instance terminalGaussianCharted : ChartedSpace H F.M := F.charted
local instance terminalGaussianSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalGaussianT2 : T2Space F.M := F.t2
local instance terminalGaussianSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem ancient_lCost_ge_terminal_distance_sq
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 / (2 * Real.sqrt tau) ≤
      lCost F.S T p q tau := by
  let : ConnectedSpace F.M := hF.connected
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  have htime (s : ℝ) : T - s ^ 2 ∈ ancientTimeInterval.carrier := by
    change T - s ^ 2 ≤ 0
    nlinarith [sq_nonneg s]
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  exact Perelman.lCost_ge_riemannianEDistOf_sq_div F.S F.isSolution T p q htau
    (F.S.base.metric 0) (fun s _ => htime s)
    (fun s _ => CanonicalNeighborhood.ancientModel_metric_zero_le F hF (htime s))
    (fun s _ z => (hC (T - s ^ 2) (htime s) z).1)

theorem ancient_redLength_ge_terminal_distance_sq
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 / (4 * tau) ≤
      redLength F.S T p q tau := by
  have hcost := ancient_lCost_ge_terminal_distance_sq F hF hT p q htau
  have hquot := div_le_div_of_nonneg_right hcost
    (show 0 ≤ 2 * Real.sqrt tau by positivity)
  rw [div_div, show (2 * Real.sqrt tau) * (2 * Real.sqrt tau) = 4 * tau by
    nlinarith [Real.sq_sqrt htau.le]] at hquot
  exact hquot

theorem ancient_redDensity_le_terminal_gaussian
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    redDensity F.S T p q tau ≤
      Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
      Real.exp (-(1 / (4 * tau)) * (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2) := by
  have hlength := ancient_redLength_ge_terminal_distance_sq F hF hT p q htau
  rw [redDensity, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : -(1 / (4 * tau)) * (riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 =
      -(riemannianEDistOf (F.S.base.metric 0) p q).toReal ^ 2 / (4 * tau) := by ring
  rw [heq, neg_div]
  simp only [neg_mul]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
