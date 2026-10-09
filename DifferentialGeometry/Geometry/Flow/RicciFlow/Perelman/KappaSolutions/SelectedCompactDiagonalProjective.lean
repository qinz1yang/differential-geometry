import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SelectedQuotientTubeChains
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDiagonalCap

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.SphereSeparation
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_poleEndpoint_strongNecks_or_diagonal_canonical_with_projective_presentation_of_not_round
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M]
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F) (p : F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop) :
    ∃ (b : ℝ) (_ : b < 0) (hbmem : b ∈ ancientTimeInterval.carrier)
      (q : ℕ → F.M) (N : ℕ) (hsigma : ∀ i, 0 < tau (i + N) + b)
      (P : PointedRiemannianManifold.{u, 0, 0} I3) (phi : ℕ → ℕ)
      (Phi : PointedCGHMaps
        (poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem
          (fun i => tau (i + N)) (fun i => q (i + N)) hsigma) P phi)
      (R : SmoothRiemannianMetric I3 P.M) (bf : BumpFamily Phi)
      (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
      (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt),
      StrictMono phi ∧ R = P.metric ∧ RiemannianMetricComplete R ∧ ConnectedSpace P.M ∧
      (∀ s : ℝ, s ≤ 0 →
        MetricComplete ({ P with metric := co.gInf s } : PointedRiemannianManifold I3)) ∧
      IsSolutionOn ({ base := { metric := co.gInf } } :
        SolutionOn (I := I3) (M := P.M) ancientTimeInterval) ∧
      (∃ f : C^∞⟮I3, P.M; ℝ⟯, gradientRicciSoliton (co.gInf 0) f 1 ∧
        IsHamiltonNormalizedPotential (co.gInf 0) f ∧
        normalizedShrinkerMass (co.gInf 0) f = asymptoticReducedVolume F.S b p ∧
        normalizedShrinkerMass (co.gInf 0) f < 1 ∧
        NoncompactSpace P.M ∧
        NoncompactShrinkerIsometryModels
          ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I3) (co.gInf 0) f ∧
        ((∃ d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ P.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0, Diffeomorph.pullbackMetricCross (co.gInf t) d =
        scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      (∀ x : SpatialNeckCylinder, f (d x) = 1 + x.2 ^ 2 / 4) ∧
      let z := d.symm P.basepoint
      let e := (cylinderLineTranslation z.2).trans d
      e (z.1, 0) = P.basepoint ∧
        (∀ y : SpatialNeckCylinder, e y = d (y.1, y.2 + z.2)) ∧
        (∀ y : SpatialNeckCylinder, f (e y) = 1 + (y.2 + z.2) ^ 2 / 4) ∧
        ∀ eps : ℝ, 0 < eps → eps < 1 / 11 → ∀ᶠ i in atTop,
          ∃ nk : StrongNeck F.S eps (q (phi (co.φ i) + N)) (-tau (phi (co.φ i) + N)),
            nk.map.source = spatialNeckBuffer eps ∧
            nk.map.target = (Phi.map (co.φ i) ∘ e) '' (spatialNeckBuffer eps : Set SpatialNeckCylinder) ∧
            nk.center = z.1 ∧
            (∀ y : spatialNeckBuffer eps, nk.map y.val = Phi.map (co.φ i) (e (y : SpatialNeckCylinder))) ∧
            nk.map '' (univ ×ˢ ({0} : Set ℝ)) =
              (Phi.map (co.φ i) ∘ e) '' (univ ×ˢ ({0} : Set ℝ))) ∨
    (∃ d : (DifferentialGeometry.RealProjectivePlane × ℝ) ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ P.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (co.gInf t)
          (cylinderAntipodalQuotientDiffeomorph.trans d)) cylinderAntipodalQuotientMap
          cylinderAntipodalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      ∀ x : DifferentialGeometry.RealProjectivePlane × ℝ, f (d x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ d : DifferentialGeometry.Geometry.CylinderDiagonalQuotient ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ P.M,
      (∀ t : ℝ, ∀ ht : t ≤ 0,
        localPullMetric (Diffeomorph.pullbackMetricCross (co.gInf t) d) cylinderDiagonalQuotientMap
          cylinderDiagonalQuotientMap_isLocalDiffeomorph =
            scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num))) ∧
      (∀ x : DifferentialGeometry.Geometry.CylinderDiagonalQuotient,
        f (d x) = cylinderDiagonalQuotientPotential x) ∧
      (∀ alpha : ℝ, 0 < alpha → 2 * alpha < 1 / 11 → ∀ y : Surgery.Topology.Sphere 2,
        ∀ L R : ℝ, (neckModelTolerance alpha)⁻¹ < L → L < R → R - L < (2 * alpha)⁻¹ →
        ∃ nk : StrongNeck (co.pointedFlow Phi rfl Subset.rfl).S (neckModelTolerance alpha)
            (d (cylinderDiagonalQuotientMap (y, L))) 0,
          nk.map.source = univ ×ˢ Ioi (-L) ∧
          (∀ z : Cylinder, nk.map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
          ∀ᶠ i in atTop, ∃ ns : StrongNeck F.S (2 * alpha)
              (Phi.map (co.φ i) (d (cylinderDiagonalQuotientMap (y, L)))) (-tau (phi (co.φ i) + N)),
            ns.map = nk.map.trans (Phi.partialDiffeomorph (co.φ i)) ∧
            univ ×ˢ Icc (0 : ℝ) (R - L) ⊆ ns.map.source ∧
            ∃ chain : OrderedNeckChain F.S (2 * alpha) (-tau (phi (co.φ i) + N))
                (Phi.map (co.φ i) '' (d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L R)))),
              chain.count = 1 ∧ ∀ j, chain.centers j = Phi.map (co.φ i) (d (cylinderDiagonalQuotientMap (y, L))) ∧
                (chain.necks j).map = ns.map ∧
                chain.lo j = 0 ∧ chain.hi j = R - L) ∧
      (∀ alpha : ℝ, 0 < alpha → 2 * alpha < 1 / 11 →
        ∃ p : Cylinder, d (cylinderDiagonalQuotientMap p) = P.basepoint ∧
      ∃ L r C rsource Csource : ℝ, (neckModelTolerance alpha)⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧ 1 ≤ C ∧ 1 < rsource ∧ rsource ≤ max r 2 ∧ 1 ≤ Csource ∧
        let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
        ∃ cap : LocalCap (co.pointedFlow Phi rfl Subset.rfl).S (neckModelTolerance alpha) (d (cylinderDiagonalQuotientMap p)) 0 U,
          cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
          cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
          (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
          cap.chain.count = 1 ∧
          (∀ j, cap.chain.centers j = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
            (∀ z : Cylinder, (cap.chain.necks j).map z = d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧
          (∀ y ∈ cap.tube, 40000 < metricDistance ((co.pointedFlow Phi rfl Subset.rfl).S.base.metric 0) P.basepoint y) ∧
          (∃ K : CanonicalWitness (co.pointedFlow Phi rfl Subset.rfl).S (neckModelTolerance alpha) r C (d (cylinderDiagonalQuotientMap p)) 0,
            K.domain.carrier = U ∧ K.radius = r ∧
            ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap) ∧
          Tendsto (fun i => (tau (phi (co.φ i) + N) + b) * F.S.scalar (-tau (phi (co.φ i) + N)) (q (phi (co.φ i) + N))) atTop (𝓝 1) ∧
          ∃ B : Set P.M, IsCompact B ∧ U ⊆ interior B ∧
            ∀ᶠ i in atTop, B ⊆ Phi.source (co.φ i) ∧
              ∃ cap' : LocalCap F.S (2 * alpha) (q (phi (co.φ i) + N)) (-tau (phi (co.φ i) + N)) (Phi.map (co.φ i) '' U),
                cap'.core.carrier = Phi.map (co.φ i) '' cap.core.carrier ∧
                cap'.tube = Phi.map (co.φ i) '' cap.tube ∧
                cap'.tubeMap = cap.tubeMap.trans (Phi.partialDiffeomorph (co.φ i)) ∧
                cap'.chain.count = 1 ∧
                (∀ j, cap'.chain.centers j = Phi.map (co.φ i) (d (cylinderDiagonalQuotientMap (p.1, L))) ∧
                  (∀ z : Cylinder, (cap'.chain.necks j).map z = Phi.map (co.φ i) (d (cylinderDiagonalQuotientMap (z.1, z.2 + L)))) ∧
                  cap'.chain.lo j = 0 ∧ cap'.chain.hi j = 1) ∧
                (∀ y ∈ cap'.tube, 10000 / Real.sqrt (F.S.scalar (-tau (phi (co.φ i) + N)) (q (phi (co.φ i) + N))) ≤
                  metricDistance (F.S.base.metric (-tau (phi (co.φ i) + N))) (q (phi (co.φ i) + N)) y) ∧
                ∃ Ks : CanonicalWitness F.S (2 * alpha) (2 * max r 2) Csource
                    (q (phi (co.φ i) + N)) (-tau (phi (co.φ i) + N)),
                  Ks.domain.carrier = Phi.map (co.φ i) '' U ∧
                  Ks.radius = Real.sqrt (tau (phi (co.φ i) + N) + b) * rsource ∧
                  (∃ cap'' depth, Ks.alternative = CanonicalAlternative.cap cap'' depth ∧ HEq cap'' cap') ∧
                  IsConnected (Phi.map (co.φ i) '' U)ᶜ ∧ IsCompact (closure (Phi.map (co.φ i) '' U)ᶜ) ∧
                  Nonempty (SmoothSideClosure (Phi.map (co.φ i) '' U)ᶜ (frontier (Phi.map (co.φ i) '' U))) ∧
                  range (fun z : Surgery.Topology.Sphere 2 => Phi.map (co.φ i) (d (cylinderDiagonalQuotientMap (z, L + 1)))) =
                    frontier (Phi.map (co.φ i) '' U) ∧
                  Manifold.IsSmoothEmbedding I2 I3 ∞
                    (fun z : Surgery.Topology.Sphere 2 => Phi.map (co.φ i) (d (cylinderDiagonalQuotientMap (z, L + 1)))) ∧
                  ∃ G : PartialDiffeomorph I3 I3 ThreeSpace F.M ∞,
                    Metric.closedBall (0 : ThreeSpace) 1 ⊆ G.source ∧
                    G '' Metric.ball (0 : ThreeSpace) 1 = (Phi.map (co.φ i) '' U)ᶜ ∧
                    G '' Metric.closedBall (0 : ThreeSpace) 1 = closure (Phi.map (co.φ i) '' U)ᶜ ∧
                    G '' Metric.sphere (0 : ThreeSpace) 1 = frontier (Phi.map (co.φ i) '' U) ∧
                    ∃ e : RealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ F.M,
                      (∀ z : Cylinder, z ∈ univ ×ˢ Icc (-(L + 1)) (L + 1) →
                        e (Geometry.cylinderDiagonalQuotientDiffeomorph (cylinderDiagonalQuotientMap z)).val =
                          Phi.map (co.φ i) (d (cylinderDiagonalQuotientMap z))) ∧
                      (∀ z : Cylinder, z.2 ∈ Icc (0 : ℝ) 1 →
                        e (Geometry.cylinderDiagonalQuotientDiffeomorph
                          (cylinderDiagonalQuotientMap (z.1, L + z.2))).val = cap'.tubeMap z) ∧
                      ∃ pr : ProjectivePresentation F.M,
                        (∀ a : Surgery.Topology.Sphere 3, pr.quotient a = e (realProjectiveSpaceQuotientMap a)) ∧
                        ∃ D : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace,
                          D '' Metric.closedBall (0 : ThreeSpace) 1 = Metric.closedBall (0 : ThreeSpace) 1 ∧
                          (∀ z ∈ Metric.closedBall (0 : ThreeSpace) 1,
                            e (realProjectiveThreeAffineBallMap (L + 1) z) = G (D z)))))) ∧
      (∀ y : P.M, 0 < metricScalarAt (co.gInf 0) y) ∧
      IsAncientKappaSolution kappa (co.pointedFlow Phi rfl Subset.rfl) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ x : P.M, ∀ v w : TangentSpace I3 x,
        (co.gInf t).inner x v w = (co.gInf 0).inner x v w -
          2 * t * ricciTensor (co.gInf 0) x v w) ∧
      (∀ a c : ℝ, a ≤ c → c ≤ 0 → ∀ K : Set P.M, IsCompact K →
        ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
          Nonempty (MetricComparisonOn co.gInf
            (fun s => scaleMetric (tau (phi (co.φ i) + N) + b)⁻¹
              (inv_pos.mpr (hsigma (phi (co.φ i))))
              (F.S.base.metric (-tau (phi (co.φ i) + N) +
                (tau (phi (co.φ i) + N) + b) * s)))
            (Phi.map (co.φ i)) K (Icc a c) order eps)) ∧
      (∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn (fun theta => co.gInf (1 - theta))
          (backwardScaledMetric F.S (tau (phi (co.φ i) + N)) (htau (phi (co.φ i) + N)))
          (Phi.map (co.φ i)) K (Icc (1 : ℝ) 3) order eps)) ∧
      ∃ Psi : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q)
          ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I3)
          (fun i => phi (co.φ i) + N),
        (∀ i, Psi.partialDiffeomorph i = Phi.partialDiffeomorph (co.φ i)) ∧
        ∃ C : MetricConvergenceData Psi,
          (∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i) ∧
          (∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric) := by
  obtain ⟨b, hb, hbmem, q, N, hsigma, P, phi, Phi, R, bf, hsrc, htgt, co,
      hphi, hRP, hR, hconn, hcomplete, hsolution, hf, hscalar, hG, hflow, hcomparison, hback,
      Psi, hPsi, C, hC, href⟩ :=
    exists_poleEndpoint_strongNecks_or_quotient_tube_chains_of_not_round F hF hnotround p tau htau hescape
  obtain ⟨f, hsol, hnormal, hmass, hmasslt, hnoncompact, hmodels, hcases⟩ := hf
  let _ : ConnectedSpace P.M := hconn
  let Q : PointedRiemannianManifold.{u, 0, 0} I3 := { P with metric := co.gInf 0 }
  let PsiDirect : PointedRiemannianConvergenceMaps (backwardSliceSequence F tau htau q) Q
      (fun i => phi (co.φ i) + N) := {
    partialDiffeomorph i := Phi.partialDiffeomorph (co.φ i)
    source_exhausts := (Phi.compSubseq co.φ co.strictMono).source_exhausts
    base_mem i := Phi.base_mem (co.φ i)
    basepoint_map i := Phi.basepoint_map (co.φ i) }
  have hcompDirect : ∀ K : Set Q.M, IsCompact K → ∀ A : ℝ, 0 < A → ∀ order : ℕ,
      ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
        Nonempty (MetricComparisonOn (co.pointedFlow Phi rfl Subset.rfl).S.base.metric
          (fun s => scaleMetric (tau (phi (co.φ i) + N) + b)⁻¹
            (inv_pos.mpr (hsigma (phi (co.φ i))))
            (F.S.base.metric (-tau (phi (co.φ i) + N) + (tau (phi (co.φ i) + N) + b) * s)))
          (PsiDirect.map i) K (Icc (-A) 0) order delta) := by
    intro K hK A hA order delta hdelta
    exact hcomparison (-A) 0 (by linarith) le_rfl K hK order delta hdelta
  refine ⟨b, hb, hbmem, q, N, hsigma, P, phi, Phi, R, bf, hsrc, htgt, co,
    hphi, hRP, hR, hconn, hcomplete, hsolution,
    ⟨f, hsol, hnormal, hmass, hmasslt, hnoncompact, hmodels, ?_⟩,
    hscalar, hG, hflow, hcomparison, hback, Psi, hPsi, C, hC, href⟩
  rcases hcases with hunquotiented | hantipodal | ⟨d, hd, hf, htubes⟩
  · exact Or.inl hunquotiented
  · exact Or.inr (Or.inl hantipodal)
  · refine Or.inr (Or.inr ⟨d, hd, hf, htubes, ?_⟩)
    intro alpha ha hsmall
    exact exists_diagonal_basepoint_canonical_transport_with_projective_presentation F hF tau htau q PsiDirect
      (co.pointedFlow Phi rfl Subset.rfl).S hsolution ⟨hcomplete 0 le_rfl⟩ d hd b
      (fun i => hsigma (phi (co.φ i))) hcompDirect ha hsmall

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
