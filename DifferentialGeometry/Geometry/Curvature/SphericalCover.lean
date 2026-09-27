import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveCover
import DifferentialGeometry.Geometry.Curvature.Metric.Conditions
import DifferentialGeometry.Topology.ThreeManifold.Closed
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Covering.FiniteFundamentalGroup
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section
open Metric Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold DifferentialGeometry.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [SigmaCompactSpace M]

theorem exists_spherical_cover_of_admits_constant_positive_sectional_curvature
    (hM : isClosedThreeManifold (I := 𝓡 3) (M := M))
    (hconst : admitsConstantPositiveSectionalCurvature (I := 𝓡 3) (M := M)) :
    (∃ p : SphereThree → M, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) ∧
      ∀ x : M, Finite (FundamentalGroup M x) := by
  let : CompactSpace M := hM.1
  let : ConnectedSpace M := hM.2.1
  let : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := 𝓡 3) (M := M)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
    ⟨by norm_num⟩
  obtain ⟨g, c, hc, hsec⟩ := hconst
  obtain ⟨d, _⟩ := sphereCover_one (A := EuclideanSpace ℝ (Fin 4)) (n := 3)
    (by norm_num) g c hc hsec (sphereBasisPt 0) (sphereBasisPt 1)
    (sphereBasisPt_ne (by decide)) (sphereBasisPt_ne_neg (by decide))
  let p : SphereThree → M := Riemannian.Topology.UniversalCover.proj ∘ d
  have hp : IsCoveringMap p :=
    (Riemannian.Topology.UniversalCover.proj_isCoveringMap (X := M)).comp_homeomorph
      d.toHomeomorph
  have hproj : Function.Surjective
      (Riemannian.Topology.UniversalCover.proj : Riemannian.Topology.UniversalCover M → M) := by
    let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    exact ⟨⟨x, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath default x)⟩, rfl⟩
  have hs : Function.Surjective p := hproj.comp d.surjective
  have hl : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p :=
    DifferentialGeometry.isLocalDiffeomorph_comp
      (Riemannian.Topology.UniversalCover.proj_localDiffeo (I := 𝓡 3) (M := M))
      d.isLocalDiffeomorph
  exact ⟨⟨p, hp, hs, hl⟩,
    finite_fundamentalGroup_of_compact_simplyConnected_cover p hp hs⟩

end DifferentialGeometry.Geometry
