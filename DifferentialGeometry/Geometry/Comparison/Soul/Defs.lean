import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Submanifold.IsometricImmersion
import DifferentialGeometry.Geometry.Geodesic.Convex
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry

section ExplicitData

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure GeodesicPreservingSoul
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) : Prop where
  nonempty : Nonempty N
  compactSpace : CompactSpace N
  connectedSpace : ConnectedSpace N
  boundaryless : BoundarylessManifold IN N
  isSmoothEmbedding : IsSmoothEmbedding IN I ∞ iota
  isometricImmersion : IsRiemannianIsometricImmersion gN gM iota
  totallyConvex : isTotallyConvex gM (Set.range iota)
  preservesGeodesics : preservesGeodesics gN gM iota

structure Soul
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M) (iota : N → M) : Prop where
  nonempty : Nonempty N
  compactSpace : CompactSpace N
  connectedSpace : ConnectedSpace N
  boundaryless : BoundarylessManifold IN N
  isSmoothEmbedding : IsSmoothEmbedding IN I ∞ iota
  isometricImmersion : IsRiemannianIsometricImmersion gN gM iota
  totallyConvex : isTotallyConvex gM (Set.range iota)
  vanishingSecondFundamentalForm :
    isometricImmersion.hasVanishingSecondFundamentalForm

end ExplicitData

def isSoul {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (S : Set M) : Prop :=
  ∃ (d : ℕ) (c : ChartedSpace (EuclideanSpace ℝ (Fin d)) S),
    letI := c
    ∃ (m : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ S),
      letI := m
      ∃ gS : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) S,
        Soul gS g (Subtype.val : S → M)

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

@[reducible] alias GeodesicPreservingSoulData := DifferentialGeometry.Geometry.GeodesicPreservingSoul
@[reducible] alias VanishingSecondFundamentalFormSoulData := DifferentialGeometry.Geometry.Soul
end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry.GeodesicPreservingSoulData

@[reducible] alias mk := DifferentialGeometry.Geometry.GeodesicPreservingSoul.mk
alias nonempty := DifferentialGeometry.Geometry.GeodesicPreservingSoul.nonempty
alias compactSpace := DifferentialGeometry.Geometry.GeodesicPreservingSoul.compactSpace
alias connectedSpace := DifferentialGeometry.Geometry.GeodesicPreservingSoul.connectedSpace
alias boundaryless := DifferentialGeometry.Geometry.GeodesicPreservingSoul.boundaryless
alias isSmoothEmbedding := DifferentialGeometry.Geometry.GeodesicPreservingSoul.isSmoothEmbedding
alias isometricImmersion := DifferentialGeometry.Geometry.GeodesicPreservingSoul.isometricImmersion
alias totallyConvex := DifferentialGeometry.Geometry.GeodesicPreservingSoul.totallyConvex
alias preservesGeodesics := DifferentialGeometry.Geometry.GeodesicPreservingSoul.preservesGeodesics
end DifferentialGeometry.Geometry.GeodesicPreservingSoulData

namespace DifferentialGeometry.Geometry.VanishingSecondFundamentalFormSoulData

@[reducible] alias mk := DifferentialGeometry.Geometry.Soul.mk
alias nonempty := DifferentialGeometry.Geometry.Soul.nonempty
alias compactSpace := DifferentialGeometry.Geometry.Soul.compactSpace
alias connectedSpace := DifferentialGeometry.Geometry.Soul.connectedSpace
alias boundaryless := DifferentialGeometry.Geometry.Soul.boundaryless
alias isSmoothEmbedding := DifferentialGeometry.Geometry.Soul.isSmoothEmbedding
alias isometricImmersion := DifferentialGeometry.Geometry.Soul.isometricImmersion
alias totallyConvex := DifferentialGeometry.Geometry.Soul.totallyConvex
alias vanishingSecondFundamentalForm := DifferentialGeometry.Geometry.Soul.vanishingSecondFundamentalForm

end DifferentialGeometry.Geometry.VanishingSecondFundamentalFormSoulData
