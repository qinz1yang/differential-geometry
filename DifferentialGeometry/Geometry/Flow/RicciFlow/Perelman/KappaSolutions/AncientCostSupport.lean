import DifferentialGeometry.Geometry.Comparison.Variation.Curve.FixedInitialGerm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.EndpointVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.TailVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EndpointPairing

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance supportTopology : TopologicalSpace F.M := F.topology
local instance supportCharted : ChartedSpace H F.M := F.charted
local instance supportSmooth : IsManifold I ∞ F.M := F.smooth
local instance supportT2 : T2Space F.M := F.t2
local instance supportSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_redLength_upper_support_of_ancient_minimizer
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) {tau : ℝ} (htau : 0 < tau)
    (alpha beta : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (halpha0 : alpha 0 = p)
    (hgeo : IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)))
    (hcost : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 p (alpha (Real.sqrt tau)) tau)
    (hbeta : IsGeodesicAt (I := I) (F.S.base.metric (-tau)) beta 0)
    (hbeta0 : beta 0 = alpha (Real.sqrt tau)) :
    ∃ phi : ℝ → ℝ, ∃ d : ℝ,
      phi 0 = redLength F.S 0 p (beta 0) tau ∧
      (fun r ↦ redLength F.S 0 p (beta r) tau) ≤ᶠ[𝓝 (0 : ℝ)] phi ∧
      HasDerivAt phi d 0 ∧
      d ≤ Real.sqrt 3 / Real.sqrt tau * Real.sqrt (redLength F.S 0 p (beta 0) tau) *
        Real.sqrt ((F.S.base.metric (-tau)).inner (beta 0)
          (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0)) := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  obtain ⟨c, hc, f, hf, hcenter, hcenterGeo, _hfix, hgerm, hend, hvel⟩ :=
    exists_lRegularizedGeodesic_tail_variation F.S F.isSolution 0 hb hgeo
      (by simpa only [Real.sq_sqrt htau.le, zero_sub] using hbeta) hbeta0
  obtain ⟨fnew, hfnew, hnew0, hnewfix, hnewend⟩ :=
    exists_smooth_variation_fixed_initial_germ f hf hc.2
  have hnewcenter : EqOn (fnew 0) alpha (Icc c (Real.sqrt tau)) := by
    rwa [hnew0]
  have hnewGeo : IsLRegularizedGeodesicOn F.S 0 (fnew 0) (Icc c (Real.sqrt tau)) := by
    rwa [hnew0]
  have hfixed : ∀ r, fnew r =ᶠ[𝓝 c] alpha := fun r ↦ (hnewfix r).trans hgerm
  have hback : ∀ s ∈ Icc (0 : ℝ) (Real.sqrt tau), 0 - s ^ 2 ∈ ancientTimeInterval.carrier := by
    intro s _hs
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg s)
  obtain ⟨B, hB⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  have hRm : ∃ B : ℝ, ∀ t ∈ Icc (0 - (Real.sqrt tau) ^ 2) 0, ∀ y : F.M,
      Tensor0SBundle.normSq0S (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ B := by
    refine ⟨B, fun t ht y ↦ hB t ?_ y⟩
    simpa only [ancientTimeInterval_carrier, mem_Iic] using ht.2
  have hmin : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 (alpha 0) (alpha (Real.sqrt tau)) ((Real.sqrt tau) ^ 2) := by
    simpa only [halpha0, Real.sq_sqrt htau.le] using hcost
  obtain ⟨phi, hphi, hupper, hd⟩ :=
    exists_redLength_upper_support_of_fixed_germ_variation F.S F.isSolution 0 (Real.sqrt tau)
      hc.1 hc.2 alpha halpha hmin fnew hfnew hnewcenter hnewGeo hfixed hback hRm
  have hendNew : (fun r ↦ fnew r (Real.sqrt tau)) =ᶠ[𝓝 (0 : ℝ)] beta :=
    Filter.EventuallyEq.trans (Filter.Eventually.of_forall hnewend) hend
  have hbase : fnew 0 (Real.sqrt tau) = beta 0 := hendNew.self_of_nhds
  have hvelNew : lVelocity (I := I) (fun r ↦ fnew r (Real.sqrt tau)) 0 =
      lVelocity (I := I) beta 0 := by
    unfold lVelocity
    exact congrArg (fun f : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) →L[ℝ] TangentSpace I (beta 0) ↦ f (1 : ℝ)) hendNew.mfderiv_eq
  have hcentralVel : lVelocity (I := I) (fnew 0) (Real.sqrt tau) =
      lVelocity (I := I) alpha (Real.sqrt tau) := by rw [hnew0]; exact hvel
  let d : ℝ := (F.S.base.metric (-tau)).inner (beta 0)
    (lVelocity (I := I) beta 0) (lVelocity (I := I) alpha (Real.sqrt tau)) / (2 * Real.sqrt tau)
  have hderiv : HasDerivAt phi d 0 := by
    simp only [Real.sq_sqrt htau.le, zero_sub, hvelNew, hcentralVel] at hd
    dsimp only [d]
    convert hd using 1
    exact congrArg (fun q : F.M ↦ (F.S.base.metric (-tau)).inner q
      (lVelocity (I := I) beta 0) (lVelocity (I := I) alpha (Real.sqrt tau)) /
        (2 * Real.sqrt tau)) hbase.symm
  refine ⟨phi, d, ?_, ?_, hderiv, ?_⟩
  · simpa only [halpha0, Real.sq_sqrt htau.le, hbeta0] using hphi
  · filter_upwards [hendNew] with r hr
    simpa only [halpha0, Real.sq_sqrt htau.le, hr] using hupper r
  · have hp := abs_lRegularized_endpoint_pairing_le_of_ancient_action_eq_lCost
      F hF alpha halpha p htau (fun s hs ↦ hgeo s ⟨hs.1, hs.2.le⟩) hcost
      (lVelocity (I := I) beta 0)
    have hp' : |d| ≤ Real.sqrt 3 / Real.sqrt tau * Real.sqrt (redLength F.S 0 p (beta 0) tau) *
        Real.sqrt ((F.S.base.metric (-tau)).inner (beta 0)
          (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0)) := by
      dsimp only [d]
      have hmetric : (F.S.base.metric (-tau)).inner (beta 0) =
          (F.S.base.metric (-tau)).inner (alpha (Real.sqrt tau)) := congrArg _ hbeta0
      rw [hmetric, hbeta0]
      convert hp using 1
    exact (le_abs_self d).trans hp'

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
