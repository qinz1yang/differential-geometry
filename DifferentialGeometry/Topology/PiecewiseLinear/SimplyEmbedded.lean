import DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronPush

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

end DifferentialGeometry.Topology.PiecewiseLinear
