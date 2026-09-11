import DifferentialGeometry.Analysis.Integration.Gaussian.VolumeTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness


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

local instance twoPointCostTopology : TopologicalSpace F.M := F.topology
local instance twoPointCostCharted : ChartedSpace H F.M := F.charted
local instance twoPointCostSmooth : IsManifold I ∞ F.M := F.smooth
local instance twoPointCostT2 : T2Space F.M := F.t2
local instance twoPointCostSigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem ancientKappaThree_reducedCost_two_point
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (p q : F.M) {tau : ℝ} (htau : 0 < tau) :
    collapsedVolumeChi *
        ((riemannianEDistOf (F.S.base.metric (-tau)) p q).toReal) ^ 2 / tau - 1 -
      lCost F.S 0 p p tau / (2 * Real.sqrt tau) ≤
        lCost F.S 0 p q tau / (2 * Real.sqrt tau) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
