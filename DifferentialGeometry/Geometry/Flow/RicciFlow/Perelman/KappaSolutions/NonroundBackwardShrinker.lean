import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardSpaceForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkerMassClassification

section
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} I ancientTimeInterval)
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem backwardSliceShrinker_noncompact_of_not_round
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (hnotround : ¬ IsShrinkingSphericalSpaceFormFlow F)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i)
    (hescape : Filter.Tendsto tau Filter.atTop Filter.atTop)
    (q : ℕ → F.M) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (Phi : PointedRiemannianConvergenceMaps (I := I)
      (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hconnected : ConnectedSpace L.M)
    (hnonflat : ∃ x : L.M, metricScalarAt L.metric x ≠ 0)
    (hnco : ∀ x : L.M, ∀ (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x),
      0 ≤ ∑ i, ∑ j, c i * c j * metricRm04StandardAt L.metric x (v i) (w i) (w j) (v j))
    (f : C^∞⟮I, L.M; ℝ⟯) (hsoliton : gradientRicciSoliton L.metric f 1)
    (hnormal : IsHamiltonNormalizedPotential L.metric f) :
    NoncompactSpace L.M := by
  apply not_compactSpace_iff.mp
  intro hcompact
  obtain ⟨hscalar, hEin⟩ := normalized_nonflat_three_shrinker_round
    L hdim hconnected hnonflat hnco f hsoliton hnormal hcompact
  obtain ⟨hT, D, e, hmetric⟩ :=
    ancient_sphericalSpaceFormFlow_of_round_backward_convergence F hdim hconn
      tau htau hescape q hphi Phi C hcanonical hcompact (by norm_num : 0 < (3 : ℝ) / 2)
      hscalar hEin
  exact hnotround ⟨3 / (2 * F.S.scalar 0 F.basepoint), hT, D, e, hmetric⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
