import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrFlowCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrLimitGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalNormalizedNeck
import DifferentialGeometry.Geometry.Comparison.Soul.PositiveEuclidean

set_option autoImplicit false
noncomputable section
open Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem ancient_kappa_three_exists_escaping_spatial_neck_centers_of_diffeomorph_euclidean
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    (he : Nonempty (F.M ≃ₘ⟮I3, 𝓡 3⟯ ThreeSpace)) (p : F.M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (mark : SpatialNeckSphere) (centers : ℕ → F.M),
      (∀ i, Nonempty (SpatialNeckWitness (F.S.base.metric 0) mark (centers i) epsilon)) ∧
      Tendsto (fun i => (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal)
        atTop atTop ∧
      Tendsto (fun i => Real.sqrt (F.S.scalar 0 (centers i)) *
        (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop := by
  have hnoncompact : NoncompactSpace F.M := by
    obtain ⟨e⟩ := he
    exact e.symm.toHomeomorph.isClosedEmbedding.noncompactSpace
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  let hK := ancientKappaThree_toKLim F hF hdim
  obtain ⟨x, r, eps, hQ, hr, heps, hanti, hepsLimit, hdisjoint,
      hescape, hQr, hratio, hexpand, hscaled, hlarge, hlocal,
      hterms, hbase, hcurvature, L, phi, hphi, Phi, hconnected, hcomplete, hconv⟩ :=
    ancientKappaThree_exists_ascr_ancient_limit F hF hdim hnoncompact p
  have hlocal4 (i : ℕ) (z : F.M)
      (hz : (riemannianEDistOf (F.S.base.metric 0) z (x i)).toReal < r i) :
      F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i) :=
    (hlocal i z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith [(heps i).2]) (hQ i).le)
  have hcanonical : ∀ t ≤ (0 : ℝ),
      ∃ C : MetricConvergenceData
          (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t) k := by
    intro t ht
    obtain ⟨C, hC, hreference⟩ := hconv t ht
    exact ⟨C, hC⟩
  obtain ⟨hL, hLbase, hLscalar, hLrm⟩ :=
    terminalCurvatureNormalizedFlowSeq_ancient_limit_geometry F hF hK hdim
      x r hQ hlocal4 hexpand L phi hphi Phi hconnected hcomplete hcanonical
  obtain ⟨C0, hC0⟩ := hcanonical 0 le_rfl
  obtain ⟨mark, cylinder, hmarked, hmetric, hnecks⟩ :=
    terminalCurvatureNormalizedFlowSeq_limit_eventually_spatialNeckWitness
      F L hK hL hdim p x hQ hescape hscaled hphi
      (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
        (L := L) (phi := phi) 0) C0 hC0 he
  obtain ⟨N, hN⟩ := hnecks epsilon hepsilon
  let tail : ℕ → ℕ := fun i => N + i
  have htail : StrictMono tail := fun i j hij => Nat.add_lt_add_left hij N
  refine ⟨mark, fun i => x (phi (tail i)), ?_,
    hescape.comp (hphi.tendsto_atTop.comp htail.tendsto_atTop),
    hscaled.comp (hphi.tendsto_atTop.comp htail.tendsto_atTop)⟩
  intro i
  obtain ⟨W, hW⟩ := hN (tail i) (Nat.le_add_right N i)
  exact ⟨W⟩

attribute [local instance] PointedFlowData.t2TangentBundle

open scoped Bundle

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem ancient_kappa_three_exists_escaping_spatial_neck_centers_of_positive_sectional
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (F.S.base.metric 0))
    (p : F.M) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (mark : SpatialNeckSphere) (centers : ℕ → F.M),
      (∀ i, Nonempty (SpatialNeckWitness (F.S.base.metric 0) mark (centers i) epsilon)) ∧
      Tendsto (fun i => (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal)
        atTop atTop ∧
      Tendsto (fun i => Real.sqrt (F.S.scalar 0 (centers i)) *
        (riemannianEDistOf (F.S.base.metric 0) p (centers i)).toReal) atTop atTop := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NoncompactSpace F.M := hnoncompact
  let g := F.S.base.metric 0
  have hcomplete : RiemannianMetricComplete (I := I3) g := ⟨hF.complete 0 (by simp)⟩
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I3 F.M
  let _ : T3Space F.M := inferInstance
  let _ : Bundle.RiemannianBundle (fun z : F.M => TangentSpace I3 z) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : F.M => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  let _ : EMetricSpace F.M := EMetricSpace.ofRiemannianMetric I3 F.M
  let _ : CompleteSpace F.M := hcomplete.complete
  have hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := I3) g :=
    fun z v => DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I3) g z v
  let _ : MetricSpace F.M := DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace
    (I := I3) (M := F.M)
  let _ : IsRiemannianManifold I3 F.M := ⟨fun z w => by
    rw [edist_dist, DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_dist_eq
      (I := I3)]
    exact ENNReal.ofReal_toReal
      (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
        (I := I3) z w)⟩
  obtain ⟨soul, e, hsoul⟩ :=
    DifferentialGeometry.Geometry.Topology.exists_diffeomorph_euclidean_three_of_positiveSectionalCurvature
      g hEnorm hsec (by simp [ThreeSpace])
  exact ancient_kappa_three_exists_escaping_spatial_neck_centers_of_diffeomorph_euclidean
    F hF ⟨e⟩ p hepsilon

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
