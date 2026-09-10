import DifferentialGeometry.Geometry.Curvature.AncientSplitting
import DifferentialGeometry.Geometry.Curvature.PositiveRicciCover
import DifferentialGeometry.Geometry.Curvature.PositiveSectionalCover
import DifferentialGeometry.Geometry.Curvature.PositiveSectionalRicci
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section
open Manifold Topology
open scoped ContDiff

namespace Poincare.Geometry

open DifferentialGeometry DifferentialGeometry.Topology.ThreeManifold
open Poincare.Topology

theorem exists_standard_cover_of_ancient_spatial_splitting
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric (𝓡 3) M}
    (hcomplete : RiemannianMetricComplete g)
    (hsplit : ancientKappaSolutionSpatialSplitting g)
    (hCG : NoncompactSpace M → cheegerGromollSoulTheorem g) :
    (∀ x : M, Finite (FundamentalGroup M x)) ∧
      ((∃ p : EuclideanSpace ℝ (Fin 3) → M,
        IsCoveringMap p ∧ Function.Surjective p ∧
          IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) ∨
       (∃ p : SphereThree → M,
        IsCoveringMap p ∧ Function.Surjective p ∧
          IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) ∨
       ∃ (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) (p : U → M),
        IsCoveringMap p ∧ Function.Surjective p ∧
          IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) := by
  change HasPositiveSectionalCurvature g ∨ Nonempty (smoothCylinderCover M) at hsplit
  rcases hsplit with hsec | hcover
  · by_cases hc : CompactSpace M
    · let : CompactSpace M := hc
      have hM : isClosedThreeManifold (I := 𝓡 3) (M := M) :=
        ⟨hc, inferInstance, inferInstance, by simp⟩
      obtain ⟨hcover, hfinite⟩ := exists_spherical_cover_of_admits_positive_ricci hM
        ⟨g, hsec.positive_ricci_metric (by simp)⟩
      exact ⟨hfinite, Or.inr (Or.inl hcover)⟩
    · let : NoncompactSpace M := not_compactSpace_iff.mp hc
      obtain ⟨hcover, hfinite⟩ := exists_euclidean_cover_of_cheegerGromoll
        (hCG inferInstance) hcomplete hsec
      exact ⟨hfinite, Or.inl hcover⟩
  · obtain ⟨c⟩ := hcover
    obtain ⟨p, hp, hs, hl⟩ := c.exists_euclidean_open_cover
    exact ⟨c.finite_fundamentalGroup,
      Or.inr (Or.inr ⟨Poincare.Topology.Manifold.puncturedSpace (EuclideanSpace ℝ (Fin 3)),
        p, hp, hs, hl⟩)⟩

end Poincare.Geometry
