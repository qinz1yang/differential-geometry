import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.closure_interior_of_finrank {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {P : Set E} (hP : IsPLBall (n + 1) P) :
    closure (interior P) = P := by
  let e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  have hpl : IsPiecewiseAffineOn e P :=
    (isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
      hP.isPolyhedron (subset_univ _)
  have he : IsPLHomeomorphOn e P (e '' P) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP.isPolyhedron hpl e.injective.injOn.bijOn_image
  have hball : IsPLBall (n + 1) (e '' P) := hP.of_isPLHomeomorphOn he
  apply e.injective.image_injective
  change e.toContinuousLinearEquiv.toHomeomorph '' closure (interior P) = e '' P
  rw [e.toContinuousLinearEquiv.toHomeomorph.image_closure,
    e.toContinuousLinearEquiv.toHomeomorph.image_interior]
  exact hball.closure_interior

end DifferentialGeometry.Topology.PiecewiseLinear
