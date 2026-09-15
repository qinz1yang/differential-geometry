import DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronPush
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Analysis.Convex.CompactFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def IsSimplyEmbedded (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsPLSphere 2 S ∧ ∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → IsOpen W → S ⊆ W →
    ∃ (T : Finset (EuclideanSpace ℝ (Fin 3)))
      (h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
      AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3)) ∧ T.card = 4 ∧
      IsPLHomeomorphOn h univ univ ∧
      h '' S = frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) ∧ EqOn h id Wᶜ

theorem exists_hasPushProperty_of_isSimplyEmbedded
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsSimplyEmbedded S) :
    ∃ C : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 C ∧ frontier C = S ∧
      Bornology.IsBounded C ∧ HasPushProperty C := by
  obtain ⟨T, h, hT, hcard, hh, himage, -⟩ := hS.2 univ convex_univ isOpen_univ (subset_univ S)
  have hpush := (hasPushProperty_convexHull_simplex T hT hcard).image hh.homeomorph_symm
  refine ⟨h.symm '' convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))), hpush.1, ?_,
    hpush.1.isPolyhedron.isCompact.isBounded, hpush⟩
  rw [← h.symm.image_frontier, ← himage, h.image_symm, h.injective.preimage_image]

theorem exists_hasPushProperty_subset_of_isSimplyEmbedded
    {S W : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsSimplyEmbedded S)
    (hW : Convex ℝ W) (hWo : IsOpen W) (hSW : S ⊆ W) :
    ∃ C : Set (EuclideanSpace ℝ (Fin 3)), HasPushProperty C ∧ frontier C = S ∧ C ⊆ W := by
  obtain ⟨C, hC, hfront, -, hpush⟩ := exists_hasPushProperty_of_isSimplyEmbedded hS
  exact ⟨C, hpush, hfront,
    DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_convex_open
      hC.isPolyhedron.isCompact hW hWo (hfront.symm ▸ hSW)⟩

theorem hasPushProperty_of_isSimplyEmbedded_frontier
    {C : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (hS : IsSimplyEmbedded (frontier C)) : HasPushProperty C := by
  obtain ⟨T, h, hT, hcard, hh, himage, -⟩ :=
    hS.2 univ convex_univ isOpen_univ (subset_univ _)
  have hfront : frontier (h '' C) = frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) := by
    rw [← h.image_frontier, himage]
  have hint : (interior (h '' C)).Nonempty := by
    rw [← h.image_interior]
    exact hC.interior_nonempty.image h
  have heq := DifferentialGeometry.Analysis.IsCompact.eq_of_frontier_eq_convex_closed
    (hC.isPolyhedron.isCompact.image h.continuous) hint (convex_convexHull ℝ _)
    ((hasPushProperty_convexHull_simplex T hT hcard).1.isPolyhedron.isCompact.isClosed) hfront
  have hpush := (hasPushProperty_convexHull_simplex T hT hcard).image hh.homeomorph_symm
  rwa [← heq, h.image_symm, h.injective.preimage_image] at hpush

end DifferentialGeometry.Topology.PiecewiseLinear
