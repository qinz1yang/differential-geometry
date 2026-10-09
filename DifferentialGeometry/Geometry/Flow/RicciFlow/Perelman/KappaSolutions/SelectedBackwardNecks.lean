import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonroundShrinkerFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardCylinderNecks

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_poleEndpoint_strongNecks_or_quotient_models_of_not_round
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
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
      ∀ x : DifferentialGeometry.Geometry.CylinderDiagonalQuotient,
        f (d x) = cylinderDiagonalQuotientPotential x))) ∧
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
    exists_poleEndpoint_cylindrical_flow_limit_of_not_round F hF hnotround p tau htau hescape
  obtain ⟨f, hsol, hnormal, hmass, hmasslt, hnoncompact, hmodels, hcases⟩ := hf
  have hmapeq (i : ℕ) : Psi.map i = Phi.map (co.φ i) := by
    funext y
    exact congrArg (fun e => e y) (hPsi i)
  have hbackPsi : ∀ K : Set P.M, IsCompact K → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn (fun theta => co.gInf (1 - theta))
        (backwardScaledMetric F.S (tau (phi (co.φ i) + N)) (htau (phi (co.φ i) + N)))
        (Psi.map i) K (Icc (1 : ℝ) 3) order eps) := by
    intro K hK order eps heps
    simpa only [hmapeq] using hback K hK order eps heps
  refine ⟨b, hb, hbmem, q, N, hsigma, P, phi, Phi, R, bf, hsrc, htgt, co,
    hphi, hRP, hR, hconn, hcomplete, hsolution,
    ⟨f, hsol, hnormal, hmass, hmasslt, hnoncompact, hmodels, ?_⟩,
    hscalar, hG, hflow, hcomparison, hback, Psi, hPsi, C, hC, href⟩
  rcases hcases with ⟨d, hd, hf⟩ | hantipodal | hdiagonal
  · have hn := backwardCylinderLimit_eventually_strongNeck_with_map F tau htau q Psi C hC
      co.gInf rfl hbackPsi d hd
    dsimp only at hn
    obtain ⟨hmark, hmap, hnecks⟩ := hn
    refine Or.inl ⟨d, hd, hf, hmark, hmap, ?_, ?_⟩
    · intro y
      exact hf (y.1, y.2 + (d.symm P.basepoint).2)
    · intro eps heps hsmall
      filter_upwards [hnecks eps heps hsmall] with i hi
      obtain ⟨nk, hsource, htarget, hcenter, hnk, hcentral⟩ := hi
      refine ⟨nk, hsource, ?_, hcenter, ?_, ?_⟩
      · apply htarget.trans
        apply image_congr
        intro y _hy
        exact congrFun (hmapeq i) (((cylinderLineTranslation (d.symm P.basepoint).2).trans d) y)
      · intro y
        exact (hnk y).trans (congrFun (hmapeq i)
          (((cylinderLineTranslation (d.symm P.basepoint).2).trans d) y.val))
      · apply hcentral.trans
        apply image_congr
        intro y _hy
        exact congrFun (hmapeq i) (((cylinderLineTranslation (d.symm P.basepoint).2).trans d) y)
  · exact Or.inr (Or.inl hantipodal)
  · exact Or.inr (Or.inr hdiagonal)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
