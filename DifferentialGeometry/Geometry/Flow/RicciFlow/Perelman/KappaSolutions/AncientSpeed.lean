import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood Set
open scoped Manifold ContDiff
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance speedBoundTopology : TopologicalSpace F.M := F.topology
local instance speedBoundCharted : ChartedSpace H F.M := F.charted
local instance speedBoundSmooth : IsManifold I ∞ F.M := F.smooth
local instance speedBoundT2 : T2Space F.M := F.t2
local instance speedBoundSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem lRegularizedSpeedSq_le_six_action_div_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {b : ℝ} (hb : 0 < b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 b)) :
    lRegularizedSpeedSq F.S 0 alpha b ≤
      6 * lRegularizedAction F.S 0 alpha 0 b / b := by
  have henergy := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa F hF alpha halpha hb.le hgeo
  have hscalar : 0 ≤ F.S.scalar (0 - b ^ 2) (alpha b) := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply (hC (0 - b ^ 2) (by simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using (neg_nonpos.mpr (sq_nonneg b)))) (alpha b) |>.1
  dsimp only [lRegularizedLagrangian] at henergy
  change b * ((1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha b +
      2 * b ^ 2 * F.S.scalar (0 - b ^ 2) (alpha b)) ≤
    3 * lRegularizedAction F.S 0 alpha 0 b at henergy
  have hspeed : 0 ≤ lRegularizedSpeedSq F.S 0 alpha b := lRegularizedSpeedSq_nonneg F.S 0 alpha b
  have hterm : 0 ≤ 2 * b ^ 2 * F.S.scalar (0 - b ^ 2) (alpha b) := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg b)) hscalar
  have hkin : b * ((1 / 2 : ℝ) * lRegularizedSpeedSq F.S 0 alpha b) ≤
      3 * lRegularizedAction F.S 0 alpha 0 b := by
    have := henergy
    nlinarith [mul_nonneg hb.le hterm]
  apply (le_div_iff₀ hb).2
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
