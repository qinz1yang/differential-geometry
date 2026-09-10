import DifferentialGeometry.Topology.Manifold.UniversalCoverOrientation
import DifferentialGeometry.Topology.Covering.UniversalDeckGroup



noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Covering

namespace Poincare.Geometry.Riemannian

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCover_deck_diffeomorph
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (F : deckGroup (UniversalCover.proj : UniversalCover M → M)) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (UniversalCover M) (UniversalCover M) ∞,
      (∀ z, D z = F.val z) ∧
      (∀ z (v w : TangentSpace 𝓘(ℝ, E) z),
        (UniversalCover.liftedMetric g).inner (D z)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) D z v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) D z w) =
          (UniversalCover.liftedMetric g).inner z v w) ∧
      (∀ z, Orientation.map (Fin n)
        (D.mfderivToContinuousLinearEquiv (by decide) z).toLinearEquiv
          (universalCoverOrientation o z) = universalCoverOrientation o (D z)) := by
  obtain ⟨a, rfl⟩ := fundamentalGroupToDeck_surjective F
  exact ⟨UniversalCover.deckDiffeo a, fun _ => rfl,
    UniversalCover.deck_inner g a, universalCoverDeck_preserves_orientation o a⟩

end Poincare.Geometry.Riemannian
