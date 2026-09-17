import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.PrefixBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood Set MeasureTheory Bundle Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientPrefixTopology : TopologicalSpace F.M := F.topology
local instance ancientPrefixCharted : ChartedSpace H F.M := F.charted
local instance ancientPrefixSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientPrefixT2 : T2Space F.M := F.t2
local instance ancientPrefixSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem redLength_prefix_le_of_ancient_action_eq_lCost
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (x y : F.M) {s tau : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hstart : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 x (alpha (Real.sqrt tau)) tau) :
    redLength F.S 0 x (alpha (Real.sqrt s)) s ≤
      (Real.sqrt tau / Real.sqrt s) * redLength F.S 0 x y tau := by
  have hLag := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha)
      (uIcc 0 (Real.sqrt tau)) := by
    apply hLag.comp (continuous_const.prodMk continuous_id).continuousOn
    intro r hr
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg r)
  apply redLength_squareRootReparametrization_le_of_action_eq_lCost F.S 0 alpha halpha x y
    hs hst hstart hend _ hcont.intervalIntegrable hcost
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  intro r hr z
  exact (hC (0-r) (by simpa only [ancientTimeInterval_carrier, Set.mem_Iic, zero_sub] using neg_nonpos.mpr hr.1) z).1

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
