import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.AncientHalfLineLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerCylinderModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCoverEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerCover

section
set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open Surgery.Topology (ThreeSpace)

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem poleEndpointRescaledFlowSeq_isAncientKappaSolution
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) :
    IsAncientKappaSolution kappa
      ((poleEndpointRescaledFlowSeq F rfl rfl b hbmem tau q hsigma).term i) := by
  have htime : -tau i ∈ ancientTimeInterval.carrier := neg_nonpos.mpr (htau i).le
  have hcurv : normSq0S (F.S.base.metric (-tau i)) (q i) 4 (F.S.base.rm04 (-tau i) (q i)) ≠ 0 := by
    intro hzero
    have hscalar := ancientKappa_scalar_pos F hF
      (neg_nonpos.mpr (htau i).le) (q i)
    have hbound := scalar_abs_le_rm (F.S.base.metric (-tau i)) (q i)
    change |F.S.scalar (-tau i) (q i)| ≤ _ * Real.sqrt
      (normSq0S (F.S.base.metric (-tau i)) (q i) 4 (F.S.base.rm04 (-tau i) (q i))) at hbound
    rw [hzero, Real.sqrt_zero, mul_zero] at hbound
    exact hscalar.not_ge ((le_abs_self _).trans hbound)
  exact isAncientKappaSolution_curvatureNormalizedFlow_of_rmNormSq_ne_zero F hF
    (-tau i) (tau i + b)⁻¹ (inv_pos.mpr (hsigma i)) htime (q i) le_rfl (q i) hcurv

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_isAncientKappaSolution
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F rfl rfl b hbmem tau q hsigma) P phi)
    {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
    {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hconnected : ConnectedSpace P.M)
    (hcomplete : ∀ s ≤ (0 : ℝ), MetricComplete
      ({ P with metric := co.gInf s } : PointedRiemannianManifold I3))
    {f : C^∞⟮I3, P.M; ℝ⟯}
    (hmodels : NoncompactShrinkerIsometryModels
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I3) (co.gInf 0) f) :
    IsAncientKappaSolution kappa (co.pointedFlow Phi rfl Subset.rfl) := by
  apply co.pointedFlow_isAncientKappaSolution Phi rfl
    (poleEndpointRescaledFlowSeq_isAncientKappaSolution F hF b hbmem tau htau q hsigma)
    hconnected hcomplete (fun x => (hmodels.scalar_eq_one _ x).le)
  exact ⟨P.basepoint, by rw [hmodels.scalar_eq_one _ P.basepoint]; norm_num⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor0SBundle
open Surgery.Topology (ThreeSpace)

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_metric_inner_eq_sub_two_mul_ricci
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F rfl rfl b hbmem tau q hsigma) P phi)
    {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
    {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hconnected : ConnectedSpace P.M) (hnoncompact : NoncompactSpace P.M)
    (hcomplete : ∀ s ≤ (0 : ℝ), MetricComplete
      ({ P with metric := co.gInf s } : PointedRiemannianManifold I3))
    {f : C^∞⟮I3, P.M; ℝ⟯} (hsol : gradientRicciSoliton (co.gInf 0) f 1)
    (hmodels : NoncompactShrinkerIsometryModels
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I3) (co.gInf 0) f) :
    ∀ t : ℝ, t ≤ 0 → ∀ x : P.M, ∀ v w : TangentSpace I3 x,
      (co.gInf t).inner x v w = (co.gInf 0).inner x v w -
        2 * t * ricciTensor (co.gInf 0) x v w := by
  let _ : ConnectedSpace P.M := hconnected
  let _ : NoncompactSpace P.M := hnoncompact
  let _ : Inhabited P.M := ⟨P.basepoint⟩
  let _ : LocallyPathConnectedSpace P.M := ChartedSpace.locallyPathConnectedSpace ThreeSpace P.M
  let _ : SemilocallySimplyConnectedSpace P.M := manifold_semilocallySimplyConnectedSpace (I := I3)
  let G := co.pointedFlow Phi rfl Subset.rfl
  have hG := co.poleEndpoint_isAncientKappaSolution F hF b hbmem tau htau q hsigma Phi
    hconnected hcomplete hmodels
  have hnonflat : ∃ x : P.M, metricScalarAt (co.gInf 0) x ≠ 0 :=
    ⟨P.basepoint, by rw [hmodels.scalar_eq_one _ P.basepoint]; norm_num⟩
  obtain ⟨d, hd⟩ := complete_noncompact_three_shrinker_universal_cover_cylinder (co.gInf 0) f
    (by norm_num : (0 : ℝ) < 1) (by simp [ThreeSpace]) ⟨hcomplete 0 le_rfl⟩ hsol hnonflat
  obtain ⟨x, v, w, hplane, hnull⟩ := cylinderCover_exists_null_plane (co.gInf 0) 2
    (by norm_num) d (by simpa only [div_one] using hd)
  obtain ⟨C, _hcases⟩ := ancientKappa_null_plane_cylinder_branch G hG
    (by simp [ThreeSpace]) 0 le_rfl x v w hplane (by
      change metricRm04StandardAt (co.gInf 0) x v w w v = 0
      exact hnull)
  exact C.metric_inner_eq_sub_two_mul_ricci

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
