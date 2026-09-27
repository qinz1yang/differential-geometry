import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier_real_prod
    {P : Set (ℝ × ℝ)} {r : (Fin 3 → ℝ) → ℝ × ℝ}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P) :
    r '' stdSimplexBoundary 2 = frontier P := by
  let e : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  have hP : IsPolyhedron P := (show IsPLBall 2 P from ⟨r, hr⟩).isPolyhedron
  have he : IsPLHomeomorphOn e P (e '' P) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
      ((isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hP (subset_univ _)) e.injective.injOn.bijOn_image
  have h := (hr.trans he).image_stdSimplexBoundary_eq_frontier
  rw [image_comp] at h
  have hefront : e '' frontier P = frontier (e '' P) := e.toHomeomorph.image_frontier P
  rw [← hefront] at h
  exact (Set.image_injective.mpr e.injective) h

end DifferentialGeometry.Topology.PiecewiseLinear
