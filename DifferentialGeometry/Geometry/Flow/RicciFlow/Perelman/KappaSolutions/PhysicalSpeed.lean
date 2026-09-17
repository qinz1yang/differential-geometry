import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSpeed
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Reparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood Set MeasureTheory
open Bundle Filter Function DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance physicalSpeedTopology : TopologicalSpace F.M := F.topology
local instance physicalSpeedCharted : ChartedSpace H F.M := F.charted
local instance physicalSpeedSmooth : IsManifold I ∞ F.M := F.smooth
local instance physicalSpeedT2 : T2Space F.M := F.t2
local instance physicalSpeedSigma : SigmaCompactSpace F.M := F.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lSpeedSq_squareRootReparametrization_le_of_ancient_action_eq_lCost
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (x y : F.M) {s tau : ℝ} (hs : 0 < s) (hst : s ≤ tau)
    (hstart : alpha 0 = x) (hend : alpha (Real.sqrt tau) = y)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 (alpha 0) (alpha (Real.sqrt tau)) tau) :
    (F.S.base.metric (-s)).inner (squareRootReparametrization alpha s)
      (lVelocity (I := I) (squareRootReparametrization alpha) s)
      (lVelocity (I := I) (squareRootReparametrization alpha) s) ≤
      3 * Real.sqrt tau * redLength F.S 0 x y tau / (s ^ (3 / 2 : ℝ)) := by
  rw [hstart] at hcost
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have htauSqrt : 0 < Real.sqrt tau := Real.sqrt_pos.mpr (hs.trans_le hst)
  have hsqrtLe : Real.sqrt s ≤ Real.sqrt tau := Real.sqrt_le_sqrt hst
  have hLag := lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha
  have hcont : ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (Icc 0 (Real.sqrt tau)) := by
    apply hLag.comp (continuous_const.prodMk continuous_id).continuousOn
    intro r hr
    change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg r)
  have hInt : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume 0 (Real.sqrt tau) :=
    (by rw [← uIcc_of_le htauSqrt.le] at hcont; exact hcont.intervalIntegrable)
  have hIntHead : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume 0 (Real.sqrt s) :=
    hInt.mono_set (by rw [uIcc_of_le hsqrt.le, uIcc_of_le htauSqrt.le]; exact Icc_subset_Icc le_rfl hsqrtLe)
  have hIntTail : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume (Real.sqrt s) (Real.sqrt tau) :=
    hInt.mono_set (by rw [uIcc_of_le hsqrtLe, uIcc_of_le htauSqrt.le]; exact Icc_subset_Icc hsqrt.le le_rfl)
  have hscalar : ∀ r ∈ Icc 0 tau, ∀ z : F.M, 0 ≤ F.S.scalar (0-r) z := by
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    intro r hr z
    exact (hC (0-r) (by simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using neg_nonpos.mpr hr.1) z).1
  have htail : 0 ≤ lRegularizedAction F.S 0 alpha (Real.sqrt s) (Real.sqrt tau) := by
    apply intervalIntegral.integral_nonneg hsqrtLe
    intro r hr
    have hr2 : r ^ 2 ≤ tau := (pow_le_pow_left₀ (hsqrt.le.trans hr.1) hr.2 2).trans_eq (Real.sq_sqrt (hs.trans_le hst).le)
    dsimp only [lRegularizedLagrangian]
    exact add_nonneg (mul_nonneg (by norm_num) (lRegularizedSpeedSq_nonneg F.S 0 alpha r))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) (hscalar (r^2) ⟨sq_nonneg r, hr2⟩ (alpha r)))
  have hadd := lRegularizedAction_add F.S 0 alpha 0 (Real.sqrt s) (Real.sqrt tau) hIntHead hIntTail
  have hact : lRegularizedAction F.S 0 alpha 0 (Real.sqrt s) ≤ lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) := by linarith
  have hspeed := lRegularizedSpeedSq_le_six_action_div_of_ancient F hF alpha halpha hsqrt (fun r hr => hgeo r ⟨hr.1, hr.2.trans_le hsqrtLe⟩)
  have hsAct : lRegularizedAction F.S 0 alpha 0 (Real.sqrt s) ≤
      2 * Real.sqrt tau * redLength F.S 0 x y tau := by
    calc
      _ ≤ lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) := hact
      _ = lCost F.S 0 x (alpha (Real.sqrt tau)) tau := hcost
      _ = 2 * Real.sqrt tau * redLength F.S 0 x y tau := by rw [hend]; unfold redLength; field_simp [htauSqrt.ne']
  have hspeed2 : lRegularizedSpeedSq F.S 0 alpha (Real.sqrt s) ≤
      6 * (2 * Real.sqrt tau * redLength F.S 0 x y tau) / Real.sqrt s :=
    hspeed.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsAct (by norm_num)) hsqrt.le)
  have hvel := lVelocity_squareRootReparametrization_of_pos (I := I) alpha hs
  have hmetric := metric_smul2 (I := I) (F.S.base.metric (-s)) (2 * Real.sqrt s)
      (lVelocity (I := I) (squareRootReparametrization alpha) s)
  have hsq : (Real.sqrt s)^2 = s := Real.sq_sqrt hs.le
  dsimp only [lRegularizedSpeedSq] at hspeed2
  rw [Real.sq_sqrt hs.le, zero_sub] at hspeed2
  change (F.S.base.metric (-s)).inner (alpha (Real.sqrt s))
      (lVelocity (I := I) alpha (Real.sqrt s)) (lVelocity (I := I) alpha (Real.sqrt s)) ≤ _ at hspeed2
  rw [hvel] at hspeed2
  have hspeed3 := hmetric.symm.trans_le hspeed2
  dsimp only [squareRootReparametrization] at hspeed3 ⊢
  have hpower : s ^ (3 / 2 : ℝ) = s * Real.sqrt s := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpower]
  apply (le_div_iff₀ (mul_pos hs hsqrt)).mpr
  have hfactor : 2 * Real.sqrt s * (2 * Real.sqrt s) = 4 * s := by nlinarith [hsq]
  rw [hfactor] at hspeed3
  have hc := (le_div_iff₀ hsqrt).mp hspeed3
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
