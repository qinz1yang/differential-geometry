import DifferentialGeometry.Topology.PiecewiseLinear.DiskGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskContainment

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_union_sdiff_diskInterior
    {S₁ S₂ D : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsSimplyEmbedded S₁) (hS₂ : IsSimplyEmbedded S₂)
    {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) (hD : S₁ ∩ S₂ = D)
    (s : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)))
    (hs : Module.finrank ℝ s.direction = 2) (hDs : D ⊆ s) :
    IsSimplyEmbedded ((S₁ ∪ S₂) \ (D \ q '' stdSimplexBoundary 2)) := by
  have hsphere : IsPLSphere 2 ((S₁ ∪ S₂) \ (D \ q '' stdSimplexBoundary 2)) := by
    obtain ⟨T, h, hT, hcard, hh, himage, -⟩ :=
      exists_isPLHomeomorphOn_straighten_union_sdiff_diskInterior hS₁ hS₂ hq hD
        convex_univ isOpen_univ (subset_univ _)
    have hshape : IsPLSphere 2 (frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))) :=
      (isPLBall_convexHull_of_affineIndependent T hT hcard).isPLSphere_frontier
    have hback := hshape.of_isPLHomeomorphOn (hh.homeomorph_symm.restrict hshape.isPolyhedron (subset_univ _))
    rw [← himage, h.image_symm, h.injective.preimage_image] at hback
    exact hback
  refine ⟨hsphere, fun W hW hWo hSW => ?_⟩
  have hD₁ : D ⊆ S₁ := hD ▸ inter_subset_left
  have hJW : q '' stdSimplexBoundary 2 ⊆ W := by
    intro x hx
    have hxD : x ∈ D := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hq.bijOn.mapsTo hy.1
    exact hSW ⟨Or.inl (hD₁ hxD), fun h => h.2 hx⟩
  have hDW : D ⊆ W := hq.subset_convex_of_boundary_subset_of_subset_affineSubspace s hs hDs hW hWo hJW
  have hSW' : S₁ ∪ S₂ ⊆ W := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact hDW hxD
    · exact hSW ⟨hx, fun h => hxD h.1⟩
  exact exists_isPLHomeomorphOn_straighten_union_sdiff_diskInterior hS₁ hS₂ hq hD hW hWo hSW'

end DifferentialGeometry.Topology.PiecewiseLinear
