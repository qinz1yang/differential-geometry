import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientEndpoint
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance pairingTopology : TopologicalSpace F.M := F.topology
local instance pairingCharted : ChartedSpace H F.M := F.charted
local instance pairingSmooth : IsManifold I ∞ F.M := F.smooth
local instance pairingT2 : T2Space F.M := F.t2
local instance pairingSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem lRegularizedSpeedSq_le_twelve_mul_redLength_of_ancient_action_eq_lCost
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau : ℝ} (htau : 0 < tau)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau) :
    (F.S.base.metric (-tau)).inner (alpha (Real.sqrt tau))
      (lVelocity (I := I) alpha (Real.sqrt tau))
      (lVelocity (I := I) alpha (Real.sqrt tau)) ≤
      12 * redLength F.S 0 p (alpha (Real.sqrt tau)) tau := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have he := lRegularizedLagrangian_mul_le_three_mul_action_of_ancientKappa
    F hF alpha halpha hb.le hgeo
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  have hR : 0 ≤ F.S.scalar (-tau) (alpha (Real.sqrt tau)) :=
    (hC (-tau) (by simpa only [ancientTimeInterval_carrier, mem_Iic] using neg_nonpos.mpr htau.le)
      (alpha (Real.sqrt tau))).1
  rw [hcost] at he
  dsimp only [lRegularizedLagrangian] at he
  rw [Real.sq_sqrt htau.le, zero_sub] at he
  have hc : lCost F.S 0 p (alpha (Real.sqrt tau)) tau =
      2 * Real.sqrt tau * redLength F.S 0 p (alpha (Real.sqrt tau)) tau := by
    unfold redLength
    field_simp
  rw [hc] at he
  have hRterm : 0 ≤ Real.sqrt tau * (2 * tau * F.S.scalar (-tau) (alpha (Real.sqrt tau))) :=
    mul_nonneg hb.le (mul_nonneg (mul_nonneg (by norm_num) htau.le) hR)
  nlinarith

theorem abs_lRegularized_endpoint_pairing_le_of_ancient_action_eq_lCost
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (p : F.M) {tau : ℝ} (htau : 0 < tau)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioo 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (v : TangentSpace I (alpha (Real.sqrt tau))) :
    |(F.S.base.metric (-tau)).inner (alpha (Real.sqrt tau)) v
      (lVelocity (I := I) alpha (Real.sqrt tau)) / (2 * Real.sqrt tau)| ≤
      Real.sqrt 3 / Real.sqrt tau *
        Real.sqrt (redLength F.S 0 p (alpha (Real.sqrt tau)) tau) *
        Real.sqrt ((F.S.base.metric (-tau)).inner (alpha (Real.sqrt tau)) v v) := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hs := lRegularizedSpeedSq_le_twelve_mul_redLength_of_ancient_action_eq_lCost
    F hF alpha halpha p htau hgeo hcost
  let g := F.S.base.metric (-tau)
  let q := alpha (Real.sqrt tau)
  let w := lVelocity (I := I) alpha (Real.sqrt tau)
  let ell := redLength F.S 0 p q tau
  change g.inner q w w ≤ 12 * ell at hs
  have hsqrt : Real.sqrt (g.inner q w w) ≤ 2 * Real.sqrt 3 * Real.sqrt ell := by
    calc
      _ ≤ Real.sqrt (12 * ell) := Real.sqrt_le_sqrt hs
      _ = 2 * Real.sqrt 3 * Real.sqrt ell := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
        have h12 : Real.sqrt (12 : ℝ) = 2 * Real.sqrt 3 := by
          rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
          norm_num
        rw [h12]
  have hCS := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    g q v w
  have hbound := hCS.trans (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))
  change |g.inner q v w / (2 * Real.sqrt tau)| ≤
    Real.sqrt 3 / Real.sqrt tau * Real.sqrt ell * Real.sqrt (g.inner q v v)
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hb)]
  apply (div_le_iff₀ (mul_pos (by norm_num) hb)).mpr
  calc
    _ ≤ Real.sqrt (g.inner q v v) * (2 * Real.sqrt 3 * Real.sqrt ell) := hbound
    _ = Real.sqrt 3 / Real.sqrt tau * Real.sqrt ell * Real.sqrt (g.inner q v v) *
        (2 * Real.sqrt tau) := by field_simp

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
