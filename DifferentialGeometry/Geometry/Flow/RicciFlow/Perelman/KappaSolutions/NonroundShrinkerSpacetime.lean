import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointShrinkerSpacetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonroundBackwardShrinker
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerMassClassification

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

theorem exists_poleEndpoint_cylindrical_shrinker_limit_of_not_round
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
          ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I3) (co.gInf 0) f) ∧
      (∀ y : P.M, 0 < metricScalarAt (co.gInf 0) y) ∧
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
      hphi, hRP, hR, hconn, hcomplete, hsolution, hf, hscalar, hcomparison, hback,
      Psi, hPsi, C, hC, href⟩ := exists_poleEndpoint_shrinker_limit F hF p tau htau hescape
  obtain ⟨f, hsol, hnormal, hmass, hmasslt⟩ := hf
  let Q : PointedRiemannianManifold.{u, 0, 0} I3 := { P with metric := co.gInf 0 }
  have hindex : StrictMono (fun i => phi (co.φ i) + N) :=
    fun i j hij => Nat.add_lt_add_right ((hphi.comp co.strictMono) hij) N
  have hcone := backwardSliceLimit_curvatureOperator_nonnegative F hF tau htau q Psi C hC
  have hnco : ∀ x : Q.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I3 x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt Q.metric x (v i) (w i) (w j) (v j) := by
    intro x
    exact (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      Q.metric x).mp (hcone x)
  have hnonflat : ∃ x : Q.M, metricScalarAt Q.metric x ≠ 0 :=
    ⟨P.basepoint, (hscalar P.basepoint).ne'⟩
  have hnoncompact : NoncompactSpace Q.M := backwardSliceShrinker_noncompact_of_not_round
    F (by simp [ThreeSpace]) hF.connected hnotround tau htau hescape q hindex Psi C hC
      hconn hnonflat hnco f hsol hnormal
  have hmodels := noncompactShrinkerIsometryModels_of_noncompact_of_nonflat_three_shrinker
    Q (by simp [ThreeSpace]) (hcomplete 0 le_rfl) hconn hnonflat hnco f hsol hnormal
      (not_compactSpace_iff.mpr hnoncompact)
  exact ⟨b, hb, hbmem, q, N, hsigma, P, phi, Phi, R, bf, hsrc, htgt, co,
    hphi, hRP, hR, hconn, hcomplete, hsolution,
    ⟨f, hsol, hnormal, hmass, hmasslt, hnoncompact, hmodels⟩, hscalar, hcomparison, hback,
    Psi, hPsi, C, hC, href⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
