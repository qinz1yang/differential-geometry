import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedTerminalLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardSlabConstruction

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_noncompact_backwardExtension_of_not_boundedAtDistance
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ BoundedAtDistance X →
        ∃ D : ℝ, 0 < D ∧ ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
          ∃ (x : ∀ i, (X.term (f i)).M) (r : ℕ → ℝ)
            (hQ : ∀ i, 1 ≤ (X.term (f i)).S.scalar 0 (x i)),
            (∀ i, 0 < r i) ∧
            Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop ∧
            Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
            (∀ i y, metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
              metricDistance ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint y < D ∧
              (X.term (f i)).S.scalar 0 y ≤ 2 * (X.term (f i)).S.scalar 0 (x i)) ∧
            ∃ L : TerminalLimit ((X.reindex f hf).terminalCurvatureRescale x hQ),
              NoncompactSpace L.space.M ∧
              (∀ y : L.space.M, metricScalarAt L.space.metric y ≤ 2) ∧
              ∃ delta : ℝ, ∃ hd : 0 < delta,
                Nonempty (BackwardExtension L
                  (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨e₀, he₀, hterminal⟩ := exists_noncompact_terminalLimit_of_not_boundedAtDistance.{u} hkappa
  obtain ⟨e₁, he₁, hbackward⟩ := exists_backward_extension_of_model_curvature_bound
    (KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
      (I := I3) (by simp [ThreeSpace]) hkappa) hsigma hPhi
  refine ⟨min e₀ e₁, lt_min he₀ he₁, ?_⟩
  intro eps heps hle X hfail
  obtain ⟨D, hD, f, hf, x, r, hQ, hr, hlarge, hQr, hcontrol, L, hnoncompact, hupper⟩ :=
    hterminal eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X hfail
  obtain ⟨delta, hd, E⟩ :=
    hbackward eps heps (hle.trans (min_le_right _ _)) _ L
  exact ⟨D, hD, f, hf, x, r, hQ, hr, hlarge, hQr, hcontrol, L, hnoncompact, hupper, delta, hd, E⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
