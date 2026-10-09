import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.IntervalVariationBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.NormalizedSecondVariation

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientReferenceSupportTopology : TopologicalSpace F.M := F.topology
local instance ancientReferenceSupportCharted : ChartedSpace H F.M := F.charted
local instance ancientReferenceSupportSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientReferenceSupportT2 : T2Space F.M := F.t2
local instance ancientReferenceSupportSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_uniform_redLength_upper_support_norm_bounds_of_ancient :
    ∃ C : ℝ, 0 < C ∧
      ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
      {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
      {kappa : ℝ}, IsAncientKappaSolution kappa F →
      ∀ (g : SmoothRiemannianMetric I F.M) (p : F.M)
      (tau c : ℝ), 0 < tau → 0 < c → c < Real.sqrt tau →
      ∀ (beta : ℝ → F.M), IsGeodesicAt (I := I) g beta 0 →
      ∃ alpha : ℝ → F.M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = p ∧ alpha (Real.sqrt tau) = beta 0 ∧
        IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) ∧
        lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
          lCost F.S 0 p (alpha (Real.sqrt tau)) tau ∧
        ∃ f : ℝ → ℝ → F.M,
          IsSmoothVariation (I := I) f ∧
          EqOn (f 0) alpha (Icc c (Real.sqrt tau)) ∧
          IsLRegularizedGeodesicOn F.S 0 (f 0) (Icc c (Real.sqrt tau)) ∧
          (∀ r, f r =ᶠ[𝓝 c] alpha) ∧
          (fun r ↦ f r (Real.sqrt tau)) =ᶠ[𝓝 (0 : ℝ)] beta ∧
          lVelocity (I := I) (f 0) (Real.sqrt tau) =
            lVelocity (I := I) alpha (Real.sqrt tau) ∧
          let Y : ∀ s, TangentSpace I (f 0 s) :=
            fun s ↦ lVelocity (I := I) (fun r ↦ f r s) 0
          (∀ s ∈ Icc c (Real.sqrt tau),
            Real.sqrt (g.inner (f 0 s) (Y s) (Y s)) ≤
              Real.sqrt (g.inner (beta 0)
                (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0))) ∧
          (∀ s ∈ Icc c (Real.sqrt tau),
            Real.sqrt (g.inner (f 0 s)
              (covDerivAlong g (f 0) Y s) (covDerivAlong g (f 0) Y s)) ≤
              C / (Real.sqrt tau - c) * Real.sqrt (g.inner (beta 0)
                (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0))) ∧
          let phi : ℝ → ℝ := fun r ↦
            (lRegularizedAction F.S 0 alpha 0 c +
              lRegularizedAction F.S 0 (f r) c (Real.sqrt tau)) / (2 * Real.sqrt tau)
          ContDiff ℝ 2 phi ∧
          phi 0 = redLength F.S 0 p (beta 0) tau ∧
          (fun r ↦ redLength F.S 0 p (beta r) tau) ≤ᶠ[𝓝 (0 : ℝ)] phi ∧
          HasDerivAt (fun r ↦ deriv phi r)
            (lRegularizedIndex F.S 0 (f 0) Y Y c (Real.sqrt tau) / Real.sqrt tau +
              (F.S.base.metric (-tau)).inner (beta 0)
                (covDerivAlong (F.S.base.metric (-tau)) beta
                  (fun r ↦ lVelocity (I := I) beta r) 0)
                (lVelocity (I := I) (f 0) (Real.sqrt tau)) / (2 * Real.sqrt tau)) 0 := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uniform_lRegularizedGeodesic_interval_variation_norm_bounds
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ H _ I _ F kappa hF g p tau c htau hc hcb beta hbeta
  obtain ⟨alpha, halpha, hstart, hend, hgeo, hcost⟩ :=
    exists_lRegularized_minimizer_of_ancient F hF p (beta 0) htau
  obtain ⟨f, hf, hcenter, hcenterGeo, hfixed, hterminal, hvelocity,
      chi, _hchi, _hchiGerm, _hchiEnd, _hchiRange, V, _hVtotal, _hVpar,
      _hVterminal, _hVnorm, _hY, _hDY, hYbound, hDYbound⟩ :=
    hproducer F.S F.isSolution g 0 alpha beta c (Real.sqrt tau) hc hcb
      hgeo hbeta hend.symm
  have hback : ∀ s ∈ Icc (0 : ℝ) (Real.sqrt tau),
      0 - s ^ 2 ∈ ancientTimeInterval.carrier := by
    intro s _hs
    simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using
      neg_nonpos.mpr (sq_nonneg s)
  obtain ⟨B, hB⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  have hRm : ∃ B : ℝ, ∀ t ∈ Icc (0 - (Real.sqrt tau) ^ 2) 0, ∀ y : F.M,
      Tensor0SBundle.normSq0S (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ B := by
    refine ⟨B, fun t ht y ↦ hB t ?_ y⟩
    simpa only [ancientTimeInterval_carrier, mem_Iic] using ht.2
  have hmin : lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
      lCost F.S 0 (alpha 0) (alpha (Real.sqrt tau)) ((Real.sqrt tau) ^ 2) := by
    simpa only [hstart, Real.sq_sqrt htau.le] using hcost
  obtain ⟨hC2, htouch, hupper, _hderiv⟩ :=
    redLength_upper_support_of_fixed_germ_variation F.S F.isSolution 0 (Real.sqrt tau)
      hc hcb alpha halpha hmin f hf hcenter hcenterGeo hfixed hback hRm
  have hsecond := hasDerivAt_deriv_lRegularizedAction_div_of_initial_germ
    F.S F.isSolution 0 f hf c (Real.sqrt tau)
    (by simpa only [uIcc_of_le hcb.le] using hcenterGeo)
    (Filter.Eventually.of_forall fun r ↦ (hfixed r).self_of_nhds) hterminal
    (lRegularizedAction F.S 0 alpha 0 c)
  refine ⟨alpha, halpha, hstart, hend, hgeo, hcost, f, hf, hcenter,
    hcenterGeo, hfixed, hterminal, hvelocity, hYbound, hDYbound, hC2, ?_, ?_, ?_⟩
  · simpa only [hstart, hend, Real.sq_sqrt htau.le] using htouch
  · filter_upwards [hterminal] with r hr
    simpa only [hstart, Real.sq_sqrt htau.le, hr] using hupper r
  · simpa only [Real.sq_sqrt htau.le, zero_sub, lVelocity] using hsecond

theorem exists_redLength_upper_support_norm_bounds_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric I F.M) (p : F.M)
      (tau c : ℝ), 0 < tau → 0 < c → c < Real.sqrt tau →
      ∀ (beta : ℝ → F.M), IsGeodesicAt (I := I) g beta 0 →
      ∃ alpha : ℝ → F.M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = p ∧ alpha (Real.sqrt tau) = beta 0 ∧
        IsLRegularizedGeodesicOn F.S 0 alpha (Ioc 0 (Real.sqrt tau)) ∧
        lRegularizedAction F.S 0 alpha 0 (Real.sqrt tau) =
          lCost F.S 0 p (alpha (Real.sqrt tau)) tau ∧
        ∃ f : ℝ → ℝ → F.M,
          IsSmoothVariation (I := I) f ∧
          EqOn (f 0) alpha (Icc c (Real.sqrt tau)) ∧
          IsLRegularizedGeodesicOn F.S 0 (f 0) (Icc c (Real.sqrt tau)) ∧
          (∀ r, f r =ᶠ[𝓝 c] alpha) ∧
          (fun r ↦ f r (Real.sqrt tau)) =ᶠ[𝓝 (0 : ℝ)] beta ∧
          lVelocity (I := I) (f 0) (Real.sqrt tau) =
            lVelocity (I := I) alpha (Real.sqrt tau) ∧
          let Y : ∀ s, TangentSpace I (f 0 s) :=
            fun s ↦ lVelocity (I := I) (fun r ↦ f r s) 0
          (∀ s ∈ Icc c (Real.sqrt tau),
            Real.sqrt (g.inner (f 0 s) (Y s) (Y s)) ≤
              Real.sqrt (g.inner (beta 0)
                (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0))) ∧
          (∀ s ∈ Icc c (Real.sqrt tau),
            Real.sqrt (g.inner (f 0 s)
              (covDerivAlong g (f 0) Y s) (covDerivAlong g (f 0) Y s)) ≤
              C / (Real.sqrt tau - c) * Real.sqrt (g.inner (beta 0)
                (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0))) ∧
          let phi : ℝ → ℝ := fun r ↦
            (lRegularizedAction F.S 0 alpha 0 c +
              lRegularizedAction F.S 0 (f r) c (Real.sqrt tau)) / (2 * Real.sqrt tau)
          ContDiff ℝ 2 phi ∧
          phi 0 = redLength F.S 0 p (beta 0) tau ∧
          (fun r ↦ redLength F.S 0 p (beta r) tau) ≤ᶠ[𝓝 (0 : ℝ)] phi ∧
          HasDerivAt (fun r ↦ deriv phi r)
            (lRegularizedIndex F.S 0 (f 0) Y Y c (Real.sqrt tau) / Real.sqrt tau +
              (F.S.base.metric (-tau)).inner (beta 0)
                (covDerivAlong (F.S.base.metric (-tau)) beta
                  (fun r ↦ lVelocity (I := I) beta r) 0)
                (lVelocity (I := I) (f 0) (Real.sqrt tau)) / (2 * Real.sqrt tau)) 0 := by
  obtain ⟨C, hC, hproducer⟩ :=
    exists_uniform_redLength_upper_support_norm_bounds_of_ancient
  exact ⟨C, hC, hproducer F hF⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
