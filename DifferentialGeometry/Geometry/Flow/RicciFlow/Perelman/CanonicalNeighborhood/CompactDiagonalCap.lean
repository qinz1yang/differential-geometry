import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardDiagonalCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapExteriorBall
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderDiagonalProjectiveSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapGluing

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions
open DifferentialGeometry.Topology.SphereSeparation

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_diagonal_basepoint_canonical_transport_with_compact_exterior
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval) (hSm : IsSolutionOn Sm)
    [PreconnectedSpace P.M] (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ P.M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (Sm.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn Sm.base.metric
          (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
            (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
          (Phi.map i) K (Icc (-A) 0) order delta))
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∃ p : Cylinder, d (cylinderDiagonalQuotientMap p) = P.basepoint ∧
      ∃ L r C rsource Csource : ℝ, (neckModelTolerance alpha)⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧ 1 ≤ C ∧ 1 < rsource ∧ rsource ≤ max r 2 ∧ 1 ≤ Csource ∧
        let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
        ∃ cap : LocalCap Sm (neckModelTolerance alpha) (d (cylinderDiagonalQuotientMap p)) 0 U,
          cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
          cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
          (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
          cap.chain.count = 1 ∧
          (∀ j, cap.chain.centers j = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
            (∀ z : Cylinder, (cap.chain.necks j).map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          (∀ y ∈ cap.tube, 40000 < metricDistance (Sm.base.metric 0) P.basepoint y) ∧
          (∃ K : CanonicalWitness Sm (neckModelTolerance alpha) r C (d (cylinderDiagonalQuotientMap p)) 0,
            K.domain.carrier = U ∧ K.radius = r ∧
            ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap) ∧
          Tendsto (fun i => (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) atTop (𝓝 1) ∧
          ∃ B : Set P.M, IsCompact B ∧ U ⊆ interior B ∧
            ∀ᶠ i in atTop, B ⊆ Phi.source i ∧
              ∃ cap' : LocalCap F.S (2 * alpha) (q (rho i)) (-tau (rho i)) (Phi.map i '' U),
                cap'.core.carrier = Phi.map i '' cap.core.carrier ∧
                cap'.tube = Phi.map i '' cap.tube ∧
                cap'.tubeMap = cap.tubeMap.trans (Phi.partialDiffeomorph i) ∧
                cap'.chain.count = 1 ∧
                (∀ j, cap'.chain.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
                  (∀ z : Cylinder, (cap'.chain.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
                  cap'.chain.lo j = 0 ∧ cap'.chain.hi j = 1) ∧
                (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
                  metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) ∧
                ∃ Ks : CanonicalWitness F.S (2 * alpha) (2 * max r 2) Csource (q (rho i)) (-tau (rho i)),
                  Ks.domain.carrier = Phi.map i '' U ∧ Ks.radius = Real.sqrt (tau (rho i) + b) * rsource ∧
                  (∃ cap'' depth, Ks.alternative = CanonicalAlternative.cap cap'' depth ∧ HEq cap'' cap') ∧
                  IsConnected (Phi.map i '' U)ᶜ ∧ IsCompact (closure (Phi.map i '' U)ᶜ) ∧
                  Nonempty (SmoothSideClosure (Phi.map i '' U)ᶜ (frontier (Phi.map i '' U))) ∧
                  range (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) =
                    frontier (Phi.map i '' U) ∧
                  Manifold.IsSmoothEmbedding I2 I3 ∞
                    (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨p, hpbase, L, r, C, rsource, Csource, hL, hpL, hr, hC, hrs, hrsC, hCs,
      cap, hcore, htube, hmap, hcount, hchain, hfar, hK, hlim, B, hBc, hUB, hcaps⟩ :=
    exists_diagonal_basepoint_canonical_transport F hF tau htau q Phi Sm hSm hcomplete
      d hmetric b hsigma hcompare ha hsmall
  refine ⟨p, hpbase, L, r, C, rsource, Csource, hL, hpL, hr, hC, hrs, hrsC, hCs,
    cap, hcore, htube, hmap, hcount, hchain, hfar, hK, hlim, B, hBc, hUB, ?_⟩
  filter_upwards [hcaps] with i hci
  obtain ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth', Ks, hKs, hrad, hcap⟩ := hci
  have hboundary (z : Sphere 2) : cap'.tubeMap (z, 1) =
      Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1))) := by
    rw [hmap']
    change Phi.map i (cap.tubeMap (z, 1)) = _
    rw [hmap (z, 1)]
  have hrange : range (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) =
      frontier (Phi.map i '' (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))))) := by
    simpa only [hboundary] using cap'.range_outer_boundary_eq
  have hemb : Manifold.IsSmoothEmbedding I2 I3 ∞
      (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) := by
    simpa only [hboundary] using cap'.outer_boundary_isSmoothEmbedding
  have hexterior := cap'.complementary_region
  exact ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth', Ks, hKs, hrad, hcap,
    hexterior.2.1, hexterior.2.2.1, cap'.nonempty_smoothSideClosure_compl, hrange, hemb⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions
open DifferentialGeometry.Topology.SphereSeparation

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_diagonal_basepoint_canonical_transport_with_exterior_ball
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval) (hSm : IsSolutionOn Sm)
    [PreconnectedSpace P.M] (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ P.M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (Sm.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn Sm.base.metric
          (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
            (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
          (Phi.map i) K (Icc (-A) 0) order delta))
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∃ p : Cylinder, d (cylinderDiagonalQuotientMap p) = P.basepoint ∧
      ∃ L r C rsource Csource : ℝ, (neckModelTolerance alpha)⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧ 1 ≤ C ∧ 1 < rsource ∧ rsource ≤ max r 2 ∧ 1 ≤ Csource ∧
        let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
        ∃ cap : LocalCap Sm (neckModelTolerance alpha) (d (cylinderDiagonalQuotientMap p)) 0 U,
          cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
          cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
          (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
          cap.chain.count = 1 ∧
          (∀ j, cap.chain.centers j = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
            (∀ z : Cylinder, (cap.chain.necks j).map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          (∀ y ∈ cap.tube, 40000 < metricDistance (Sm.base.metric 0) P.basepoint y) ∧
          (∃ K : CanonicalWitness Sm (neckModelTolerance alpha) r C (d (cylinderDiagonalQuotientMap p)) 0,
            K.domain.carrier = U ∧ K.radius = r ∧
            ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap) ∧
          Tendsto (fun i => (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) atTop (𝓝 1) ∧
          ∃ B : Set P.M, IsCompact B ∧ U ⊆ interior B ∧
            ∀ᶠ i in atTop, B ⊆ Phi.source i ∧
              ∃ cap' : LocalCap F.S (2 * alpha) (q (rho i)) (-tau (rho i)) (Phi.map i '' U),
                cap'.core.carrier = Phi.map i '' cap.core.carrier ∧
                cap'.tube = Phi.map i '' cap.tube ∧
                cap'.tubeMap = cap.tubeMap.trans (Phi.partialDiffeomorph i) ∧
                cap'.chain.count = 1 ∧
                (∀ j, cap'.chain.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
                  (∀ z : Cylinder, (cap'.chain.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
                  cap'.chain.lo j = 0 ∧ cap'.chain.hi j = 1) ∧
                (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
                  metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) ∧
                ∃ Ks : CanonicalWitness F.S (2 * alpha) (2 * max r 2) Csource (q (rho i)) (-tau (rho i)),
                  Ks.domain.carrier = Phi.map i '' U ∧ Ks.radius = Real.sqrt (tau (rho i) + b) * rsource ∧
                  (∃ cap'' depth, Ks.alternative = CanonicalAlternative.cap cap'' depth ∧ HEq cap'' cap') ∧
                  IsConnected (Phi.map i '' U)ᶜ ∧ IsCompact (closure (Phi.map i '' U)ᶜ) ∧
                  Nonempty (SmoothSideClosure (Phi.map i '' U)ᶜ (frontier (Phi.map i '' U))) ∧
                  range (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) =
                    frontier (Phi.map i '' U) ∧
                  Manifold.IsSmoothEmbedding I2 I3 ∞
                    (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) ∧
                  ∃ G : PartialDiffeomorph I3 I3 ThreeSpace F.M ∞,
                    Metric.closedBall (0 : ThreeSpace) 1 ⊆ G.source ∧
                    G '' Metric.ball (0 : ThreeSpace) 1 = (Phi.map i '' U)ᶜ ∧
                    G '' Metric.closedBall (0 : ThreeSpace) 1 = closure (Phi.map i '' U)ᶜ ∧
                    G '' Metric.sphere (0 : ThreeSpace) 1 = frontier (Phi.map i '' U) := by
  obtain ⟨p, hpbase, L, r, C, rsource, Csource, hL, hpL, hr, hC, hrs, hrsC, hCs,
      cap, hcore, htube, hmap, hcount, hchain, hfar, hK, hlim, B, hBc, hUB, hcaps⟩ :=
    exists_diagonal_basepoint_canonical_transport_with_compact_exterior F hF tau htau q Phi Sm hSm hcomplete
      d hmetric b hsigma hcompare ha hsmall
  refine ⟨p, hpbase, L, r, C, rsource, Csource, hL, hpL, hr, hC, hrs, hrsC, hCs,
    cap, hcore, htube, hmap, hcount, hchain, hfar, hK, hlim, B, hBc, hUB, ?_⟩
  filter_upwards [hcaps] with i hci
  obtain ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth', Ks, hKs, hrad, hcap,
    hextconn, hextcompact, hsmooth, hboundary, hemb⟩ := hci
  have hsource : d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))) ⊆
      (Phi.partialDiffeomorph i).source := hUB.trans (interior_subset.trans hBi)
  have hL1 : 0 ≤ L + 1 := by
    have hpos := (inv_pos.mpr (neckModelTolerance_pos ha)).trans hL
    linarith
  obtain ⟨rp, hrp, _hrpmap, _hrange, hrpU⟩ := exists_projective_slice_diagonal_image
    d (Phi.partialDiffeomorph i) hL1 hsource
  have hball := cap'.exists_exterior_ball_of_compact_ancientKappa_of_projective_slice F hF rp hrp hrpU
  exact ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth', Ks, hKs, hrad, hcap,
    hextconn, hextcompact, hsmooth, hboundary, hemb, hball⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions
open DifferentialGeometry.Topology.SphereSeparation

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_diagonal_basepoint_canonical_transport_with_projective_presentation
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {rho : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) P rho)
    (Sm : SolutionOn (I := I3) (M := P.M) ancientTimeInterval) (hSm : IsSolutionOn Sm)
    [PreconnectedSpace P.M] (hcomplete : RiemannianMetricComplete (Sm.base.metric 0))
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ P.M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (Sm.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    (b : ℝ) (hsigma : ∀ i, 0 < tau (rho i) + b)
    (hcompare : ∀ K : Set P.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn Sm.base.metric
          (fun s => scaleMetric (tau (rho i) + b)⁻¹ (inv_pos.mpr (hsigma i))
            (F.S.base.metric (-tau (rho i) + (tau (rho i) + b) * s)))
          (Phi.map i) K (Icc (-A) 0) order delta))
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) :
    ∃ p : Cylinder, d (cylinderDiagonalQuotientMap p) = P.basepoint ∧
      ∃ L r C rsource Csource : ℝ, (neckModelTolerance alpha)⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧ 1 ≤ C ∧ 1 < rsource ∧ rsource ≤ max r 2 ∧ 1 ≤ Csource ∧
        let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
        ∃ cap : LocalCap Sm (neckModelTolerance alpha) (d (cylinderDiagonalQuotientMap p)) 0 U,
          cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
          cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
          (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
          cap.chain.count = 1 ∧
          (∀ j, cap.chain.centers j = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
            (∀ z : Cylinder, (cap.chain.necks j).map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          (∀ y ∈ cap.tube, 40000 < metricDistance (Sm.base.metric 0) P.basepoint y) ∧
          (∃ K : CanonicalWitness Sm (neckModelTolerance alpha) r C (d (cylinderDiagonalQuotientMap p)) 0,
            K.domain.carrier = U ∧ K.radius = r ∧
            ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap) ∧
          Tendsto (fun i => (tau (rho i) + b) * F.S.scalar (-tau (rho i)) (q (rho i))) atTop (𝓝 1) ∧
          ∃ B : Set P.M, IsCompact B ∧ U ⊆ interior B ∧
            ∀ᶠ i in atTop, B ⊆ Phi.source i ∧
              ∃ cap' : LocalCap F.S (2 * alpha) (q (rho i)) (-tau (rho i)) (Phi.map i '' U),
                cap'.core.carrier = Phi.map i '' cap.core.carrier ∧
                cap'.tube = Phi.map i '' cap.tube ∧
                cap'.tubeMap = cap.tubeMap.trans (Phi.partialDiffeomorph i) ∧
                cap'.chain.count = 1 ∧
                (∀ j, cap'.chain.centers j = Phi.map i (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
                  (∀ z : Cylinder, (cap'.chain.necks j).map z = Phi.map i (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
                  cap'.chain.lo j = 0 ∧ cap'.chain.hi j = 1) ∧
                (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (rho i)) (q (rho i))) ≤
                  metricDistance (F.S.base.metric (-tau (rho i))) (q (rho i)) y) ∧
                ∃ Ks : CanonicalWitness F.S (2 * alpha) (2 * max r 2) Csource (q (rho i)) (-tau (rho i)),
                  Ks.domain.carrier = Phi.map i '' U ∧ Ks.radius = Real.sqrt (tau (rho i) + b) * rsource ∧
                  (∃ cap'' depth, Ks.alternative = CanonicalAlternative.cap cap'' depth ∧ HEq cap'' cap') ∧
                  IsConnected (Phi.map i '' U)ᶜ ∧ IsCompact (closure (Phi.map i '' U)ᶜ) ∧
                  Nonempty (SmoothSideClosure (Phi.map i '' U)ᶜ (frontier (Phi.map i '' U))) ∧
                  range (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) =
                    frontier (Phi.map i '' U) ∧
                  Manifold.IsSmoothEmbedding I2 I3 ∞
                    (fun z : Sphere 2 => Phi.map i (d (cylinderDiagonalQuotientMap (z, L + 1)))) ∧
                  ∃ G : PartialDiffeomorph I3 I3 ThreeSpace F.M ∞,
                    Metric.closedBall (0 : ThreeSpace) 1 ⊆ G.source ∧
                    G '' Metric.ball (0 : ThreeSpace) 1 = (Phi.map i '' U)ᶜ ∧
                    G '' Metric.closedBall (0 : ThreeSpace) 1 = closure (Phi.map i '' U)ᶜ ∧
                    G '' Metric.sphere (0 : ThreeSpace) 1 = frontier (Phi.map i '' U) ∧
                    ∃ e : RealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ F.M,
                      (∀ z : Cylinder, z ∈ univ ×ˢ Icc (-(L + 1)) (L + 1) →
                        e (Geometry.cylinderDiagonalQuotientDiffeomorph (cylinderDiagonalQuotientMap z)).val =
                          Phi.map i (d (cylinderDiagonalQuotientMap z))) ∧
                      (∀ z : Cylinder, z.2 ∈ Icc (0 : ℝ) 1 →
                        e (Geometry.cylinderDiagonalQuotientDiffeomorph
                          (cylinderDiagonalQuotientMap (z.1, L + z.2))).val = cap'.tubeMap z) ∧
                      ∃ pr : ProjectivePresentation F.M,
                        (∀ a : Sphere 3, pr.quotient a = e (realProjectiveSpaceQuotientMap a)) ∧
                        ∃ D : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace,
                          D '' Metric.closedBall (0 : ThreeSpace) 1 = Metric.closedBall (0 : ThreeSpace) 1 ∧
                          (∀ z ∈ Metric.closedBall (0 : ThreeSpace) 1,
                            e (realProjectiveThreeAffineBallMap (L + 1) z) = G (D z)) := by
  obtain ⟨p, hpbase, L, r, C, rsource, Csource, hL, hpL, hr, hC, hrs, hrsC, hCs,
      cap, hcore, htube, hmap, hcount, hchain, hfar, hK, hlim, B, hBc, hUB, hcaps⟩ :=
    exists_diagonal_basepoint_canonical_transport_with_exterior_ball F hF tau htau q Phi Sm hSm hcomplete
      d hmetric b hsigma hcompare ha hsmall
  refine ⟨p, hpbase, L, r, C, rsource, Csource, hL, hpL, hr, hC, hrs, hrsC, hCs,
    cap, hcore, htube, hmap, hcount, hchain, hfar, hK, hlim, B, hBc, hUB, ?_⟩
  filter_upwards [hcaps] with i hci
  obtain ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth', Ks, hKs, hrad, hcap,
    hextconn, hextcompact, hsmooth, hboundary, hemb, G, hG, hGo, hGc, hGs⟩ := hci
  have hsource : d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))) ⊆
      (Phi.partialDiffeomorph i).source := hUB.trans (interior_subset.trans hBi)
  have hL1 : 0 < L + 1 := by linarith [abs_nonneg p.2]
  obtain ⟨e, heSlab, pr, hpr, D, hD, heG⟩ := exists_projectivePresentation_of_diagonal_slab_and_exterior_ball
    d (Phi.partialDiffeomorph i) hL1 hsource G hG hGo
  refine ⟨hBi, cap', hcore', htube', hmap', hcount', hchain', hdepth', Ks, hKs, hrad, hcap,
    hextconn, hextcompact, hsmooth, hboundary, hemb, G, hG, hGo, hGc, hGs, e, heSlab, ?_, pr, hpr, D, hD, heG⟩
  intro z hz
  rw [heSlab (z.1, L + z.2) ⟨mem_univ _, by constructor <;> linarith [abs_nonneg p.2, hz.1, hz.2]⟩, hmap']
  change Phi.map i (d (cylinderDiagonalQuotientMap (z.1, L + z.2))) = Phi.map i (cap.tubeMap z)
  rw [hmap z]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
