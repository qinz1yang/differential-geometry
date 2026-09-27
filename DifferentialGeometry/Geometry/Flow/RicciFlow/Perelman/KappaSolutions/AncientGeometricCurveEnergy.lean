import DifferentialGeometry.Geometry.Metric.Comparison.GeometricCurveEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalEnergy

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_ancientKappa_riemannianEDist_sq_div_le_action
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {L c : ℝ} (hL : 0 < L) (n : ℕ) (hc : L * (4 : ℝ) ^ n ≤ c) :
    ∃ j ≤ n,
      (riemannianEDistOf (F.S.base.metric 0) (alpha 0)
        (alpha (L * (4 : ℝ) ^ j))).toReal ^ 2 / (L * (4 : ℝ) ^ j) ≤
        8 * lRegularizedAction F.S 0 alpha 0 c / (n + 1 : ℝ) := by
  obtain ⟨j, hj, hsmall⟩ := exists_riemannianEDistOf_sq_div_le_curveEnergy
    (F.S.base.metric 0) alpha halpha hL n
  have hlast : 0 ≤ L * (4 : ℝ) ^ n := mul_nonneg hL.le (pow_nonneg (by norm_num) n)
  have henergy : curveEnergy (F.S.base.metric 0) alpha 0 (L * (4 : ℝ) ^ n) ≤
      2 * lRegularizedAction F.S 0 alpha 0 c := by
    have hInt := integrableOn_inner_mfderiv_self_of_contMDiffOn
      (F.S.base.metric 0) (a := 0) (b := c) halpha.contMDiffOn
    exact (curveEnergy_mono (F.S.base.metric 0) le_rfl hlast hc hInt).trans
      (curveEnergy_terminal_le_two_mul_action_of_ancient F hF alpha halpha (hlast.trans hc))
  refine ⟨j, hj, hsmall.trans ?_⟩
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ) ≤ 4))
    (by positivity : 0 ≤ (n + 1 : ℝ))
  convert h using 1
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
