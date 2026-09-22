import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedNeckLimit
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveEuclidean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreSize

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_kappa_three_exists_escaping_strong_neck_centers_of_diffeomorph_euclidean
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (he : Nonempty (F.M ≃ₘ⟮I3, 𝓡 3⟯ ThreeSpace)) (p : F.M)
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) (heta : 0 < eta) :
    ∃ (mark : SpatialNeckSphere) (centers : ℕ → F.M),
      ∃ strong : ∀ i, StrongNeckWitness F.S mark (centers i) 0 epsilon,
        ∃ spatial : ∀ i, SpatialNeckWitness (F.S.base.metric 0) mark (centers i) eta,
          (∀ i, (strong i).embedding '' spatialNeckCentralDomain epsilon = (spatial i).centralSphere) ∧
          Tendsto (fun i => (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop ∧
          Tendsto (fun i => Real.sqrt (F.S.scalar 0 (centers i)) *
            (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop := by
  obtain ⟨x, _r, _eps, _hQ, _hr, _heps, _hanti, _hepsLimit, _hdisjoint,
      hescape, _hQr, _hratio, _hexpand, hscaled, _hlocal, _hterms, _hbase,
      _L, phi, hphi, _Phi, _hL, _hLbase, _hcmp, mark, _e, _hmarked, _hmetric, hnecks⟩ :=
    ancientKappaThree_exists_ascr_strongNeck_limit_of_diffeomorph_euclidean F hF he p
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hnecks epsilon eta hepsilon hepsilon1 heta)
  let tail : ℕ → ℕ := fun i => N + i
  have htail : StrictMono tail := fun i j hij => Nat.add_lt_add_left hij N
  have hpairs (i : ℕ) := hN (tail i) (Nat.le_add_right N i)
  choose strong spatial _hstrong _hspatial hcentral using hpairs
  exact ⟨mark, fun i => x (phi (tail i)), strong, spatial, hcentral,
    hescape.comp (hphi.tendsto_atTop.comp htail.tendsto_atTop),
    hscaled.comp (hphi.tendsto_atTop.comp htail.tendsto_atTop)⟩

attribute [local instance] PointedFlowData.t2TangentBundle

open scoped Bundle

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem ancient_kappa_three_exists_escaping_strong_neck_centers_of_positive_sectional
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M)
    (hsec : HasPositiveSectionalCurvature (F.S.base.metric 0)) (p : F.M)
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) (heta : 0 < eta) :
    ∃ (mark : SpatialNeckSphere) (centers : ℕ → F.M),
      ∃ strong : ∀ i, StrongNeckWitness F.S mark (centers i) 0 epsilon,
        ∃ spatial : ∀ i, SpatialNeckWitness (F.S.base.metric 0) mark (centers i) eta,
          (∀ i, (strong i).embedding '' spatialNeckCentralDomain epsilon = (spatial i).centralSphere) ∧
          Tendsto (fun i => (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop ∧
          Tendsto (fun i => Real.sqrt (F.S.scalar 0 (centers i)) *
            (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NoncompactSpace F.M := hnoncompact
  let g := F.S.base.metric 0
  have hcomplete : RiemannianMetricComplete (I := I3) g := ⟨hF.complete 0 (by simp)⟩
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I3 F.M
  let _ : T3Space F.M := inferInstance
  let _ : Bundle.RiemannianBundle (fun z : F.M => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : F.M => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace F.M := EMetricSpace.ofRiemannianMetric I3 F.M
  let _ : CompleteSpace F.M := hcomplete.complete
  have hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g :=
    fun z v => DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  let _ : MetricSpace F.M := DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I3) (M := F.M)
  let _ : IsRiemannianManifold I3 F.M := ⟨fun z w => by
    rw [edist_dist, DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq (I := I3)]
    exact ENNReal.ofReal_toReal (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top z w)⟩
  obtain ⟨_soul, e, _hsoul⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_diffeomorph_euclidean_three_of_positiveSectionalCurvature
      g hEnorm hsec (by simp [ThreeSpace])
  exact ancient_kappa_three_exists_escaping_strong_neck_centers_of_diffeomorph_euclidean
    F hF ⟨e⟩ p hepsilon hepsilon1 heta

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_kappa_three_exists_disjoint_escaping_neckWitnesses_of_diffeomorph_euclidean
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (he : Nonempty (F.M ≃ₘ⟮I3, 𝓡 3⟯ ThreeSpace)) (p : F.M)
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (heta : 0 < eta) (hetasmall : eta ≤ spatialNeckControlEpsilon) :
    ∃ (mark : SpatialNeckSphere) (centers : ℕ → F.M),
      ∃ strong : ∀ i, StrongNeckWitness F.S mark (centers i) 0 epsilon,
        ∃ spatial : ∀ i, SpatialNeckWitness (F.S.base.metric 0) mark (centers i) eta,
          (∀ i, (strong i).embedding '' spatialNeckCentralDomain epsilon = (spatial i).centralSphere) ∧
          Pairwise (fun i j => Disjoint (spatial i).core (spatial j).core) ∧
          Tendsto (fun i => (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop ∧
          Tendsto (fun i => Real.sqrt (F.S.scalar 0 (centers i)) *
            (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop := by
  obtain ⟨x, r, _eps, hQ, hr, _heps, _hanti, _hepsLimit, hdisjoint,
      hescape, _hQr, _hratio, hexpand, hscaled, _hlocal, _hterms, _hbase,
      _L, phi, hphi, _Phi, _hL, _hLbase, _hcmp, mark, _e, _hmarked, _hmetric, hnecks⟩ :=
    ancientKappaThree_exists_ascr_strongNeck_limit_of_diffeomorph_euclidean F hF he p
  have hlarge : ∀ᶠ i in atTop, spatialNeckCoreRadiusConstant eta <
      r (phi i) * Real.sqrt (F.S.scalar 0 (x (phi i))) :=
    (hexpand.comp hphi.tendsto_atTop).eventually_gt_atTop (spatialNeckCoreRadiusConstant eta)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hnecks epsilon eta hepsilon hepsilon1 heta).and hlarge)
  let tail : ℕ → ℕ := fun i => N + i
  have htail : StrictMono tail := fun i j hij => Nat.add_lt_add_left hij N
  have hpairs (i : ℕ) := (hN (tail i) (Nat.le_add_right N i)).1
  choose strong spatial _hstrong _hspatial hcentral using hpairs
  have hcores (i : ℕ) : (spatial i).core ⊆
      {z : F.M | riemannianEDistOf (F.S.base.metric 0) z (x (phi (tail i))) < ENNReal.ofReal (r (phi (tail i)))} := by
    intro z hz
    have hbound := (spatial i).core_edist_le hetasmall hz
    have hsmall : spatialNeckCoreRadiusConstant eta /
        Real.sqrt (F.S.scalar 0 (x (phi (tail i)))) < r (phi (tail i)) :=
      (div_lt_iff₀ (Real.sqrt_pos.mpr (hQ (phi (tail i))))).mpr
        (hN (tail i) (Nat.le_add_right N i)).2
    exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr (phi (tail i))).1).mpr hsmall)
  refine ⟨mark, fun i => x (phi (tail i)), strong, spatial, hcentral, ?_,
    hescape.comp (hphi.tendsto_atTop.comp htail.tendsto_atTop),
    hscaled.comp (hphi.tendsto_atTop.comp htail.tendsto_atTop)⟩
  intro i j hij
  exact (hdisjoint (fun h => hij (htail.injective (hphi.injective h)))).mono (hcores i) (hcores j)

attribute [local instance] PointedFlowData.t2TangentBundle

open scoped Bundle

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem ancient_kappa_three_exists_disjoint_escaping_neckWitnesses_of_positive_sectional
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M)
    (hsec : HasPositiveSectionalCurvature (F.S.base.metric 0)) (p : F.M)
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) (heta : 0 < eta) (hetasmall : eta ≤ spatialNeckControlEpsilon) :
    ∃ (mark : SpatialNeckSphere) (centers : ℕ → F.M),
      ∃ strong : ∀ i, StrongNeckWitness F.S mark (centers i) 0 epsilon,
        ∃ spatial : ∀ i, SpatialNeckWitness (F.S.base.metric 0) mark (centers i) eta,
          (∀ i, (strong i).embedding '' spatialNeckCentralDomain epsilon = (spatial i).centralSphere) ∧
          Pairwise (fun i j => Disjoint (spatial i).core (spatial j).core) ∧
          Tendsto (fun i => (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop ∧
          Tendsto (fun i => Real.sqrt (F.S.scalar 0 (centers i)) *
            (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NoncompactSpace F.M := hnoncompact
  let g := F.S.base.metric 0
  have hcomplete : RiemannianMetricComplete (I := I3) g := ⟨hF.complete 0 (by simp)⟩
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I3 F.M
  let _ : T3Space F.M := inferInstance
  let _ : Bundle.RiemannianBundle (fun z : F.M => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : F.M => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace F.M := EMetricSpace.ofRiemannianMetric I3 F.M
  let _ : CompleteSpace F.M := hcomplete.complete
  have hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g :=
    fun z v => DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  let _ : MetricSpace F.M := DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I3) (M := F.M)
  let _ : IsRiemannianManifold I3 F.M := ⟨fun z w => by
    rw [edist_dist, DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq (I := I3)]
    exact ENNReal.ofReal_toReal (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top z w)⟩
  obtain ⟨_soul, e, _hsoul⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_diffeomorph_euclidean_three_of_positiveSectionalCurvature
      g hEnorm hsec (by simp [ThreeSpace])
  exact ancient_kappa_three_exists_disjoint_escaping_neckWitnesses_of_diffeomorph_euclidean
    F hF ⟨e⟩ p hepsilon hepsilon1 heta hetasmall

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
