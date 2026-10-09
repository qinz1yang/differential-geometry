import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryAffineOrbit
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryAffineRigidity
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.FiniteBoundaryOrbit
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GromovProduct
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.HorosphereMetric
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.ModelAtlas

/-!
# Consumer of the G2 intake (S-HG-INTAKE-2, suffix `_HGI2`)

Boundary-at-infinity rigidity inputs: affine conjugacy of boundary maps gives a similarity, a
nilpotent finite-index subgroup acting freely has a finite boundary orbit, and the four point
(Gromov product) inequality with the constant `log 32`.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Hyperboloid

example := @exists_similarity_of_affine_boundary_conjugacy

example := @exists_affineEquiv_boundary_conjugate_of_compact_returns

example := @exists_finite_boundary_orbit_of_isNilpotent_of_finiteIndex

example := @exists_pos_forall_exists_boundary_fixedPoint_small_displacement

example := @hasThurstonAtlas_riemannianMetric

theorem four_point_log32_HGI2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w x y z : Hyperboloid E) :
    dist w y + dist x z ≤
      max (dist w x + dist y z) (dist w z + dist x y) + Real.log 32 :=
  four_point_inequality w x y z

end DifferentialGeometry.Hyperboloid
