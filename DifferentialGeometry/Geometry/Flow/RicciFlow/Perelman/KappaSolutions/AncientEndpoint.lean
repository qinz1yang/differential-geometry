import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Ancient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set MeasureTheory Filter Function
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped Manifold ContDiff


universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientEndpointTopology : TopologicalSpace F.M := F.topology
local instance ancientEndpointCharted : ChartedSpace H F.M := F.charted
local instance ancientEndpointSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientEndpointC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance ancientEndpointT2 : T2Space F.M := F.t2
local instance ancientEndpointSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {b : ℝ} (hb : 0 ≤ b)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 b)) :
    b * lRegularizedLagrangian F.S 0 alpha b ≤ 3 * lRegularizedAction F.S 0 alpha 0 b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    exact finrank_ne_zero_of_normSq0S_ne_zero (F.S.base.metric t) x (by norm_num : 0 < 4)
      (F.S.base.rm04 t x) hx⟩
  have hcomplete : ∀ t ∈ ancientTimeInterval.regular,
      RiemannianMetricComplete (I := I) (F.S.base.metric t) :=
    fun t ht => ⟨hF.complete t (ancientTimeInterval.regular_subset ht)⟩
  have hR : ∀ t ∈ ancientTimeInterval.regular, ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht x
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t (ancientTimeInterval.regular_subset ht) x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hregular : ∀ s ∈ Ioo 0 b, Iic ((0 : ℝ) - s ^ 2) ⊆ ancientTimeInterval.regular := by
    intro s hs t ht
    rw [ancientTimeInterval_regular]
    exact lt_of_le_of_lt (mem_Iic.mp ht) (by nlinarith [sq_pos_of_pos hs.1])
  have hLag := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (Icc 0 b) := by
    apply hLag.comp (continuous_const.prodMk continuous_id).continuousOn
    intro r hr
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg r)
  exact lRegularizedLagrangian_mul_le_three_mul_action_of_ancient F.S F.isSolution hcomplete
    (ancientKappa_regularSlabBound_finrank F hF) hR 0 alpha hb hregular hgeo hcont

theorem scalar_le_three_mul_redLength_of_ancient_action_eq_lCost
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (x : F.M) {tau : ℝ} (htau : 0 < tau)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 x (alpha (Real.sqrt tau)) tau) :
    F.S.scalar (-tau) (alpha (Real.sqrt tau)) ≤
      3 * redLength F.S 0 x (alpha (Real.sqrt tau)) tau / tau := by
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have henergy := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa F hF alpha
    halpha hsqrt.le hgeo
  have hspeed := metric_inner_self_nonneg (F.S.base.metric (-tau)) (alpha (Real.sqrt tau))
    (lVelocity (I := I) alpha (Real.sqrt tau))
  rw [hcost] at henergy
  dsimp only [lRegularizedLagrangian] at henergy
  rw [Real.sq_sqrt htau.le, zero_sub] at henergy
  have hbound : 2 * Real.sqrt tau * tau * F.S.scalar (-tau) (alpha (Real.sqrt tau)) ≤
      3 * lCost F.S 0 x (alpha (Real.sqrt tau)) tau := by
    nlinarith [mul_nonneg hsqrt.le hspeed]
  unfold redLength
  apply (le_div_iff₀ htau).mpr
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos (by norm_num) hsqrt)).mpr
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
