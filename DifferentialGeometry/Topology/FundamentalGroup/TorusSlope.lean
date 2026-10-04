import DifferentialGeometry.Topology.Algebra.Group.TorusMatrix
import DifferentialGeometry.Topology.FundamentalGroup.Retraction

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace Circle

def slopeContinuousMap (v : Fin 2 → ℤ) : C(Circle, Circle × Circle) :=
  ⟨slopeMap v, (slopeMap_contMDiff v).continuous⟩

theorem slopeMap_fundamentalGroup_injective (v : Fin 2 → ℤ)
    (hv : IsCoprime (v 0) (v 1)) (z : Circle) :
    Function.Injective (FundamentalGroup.map (slopeContinuousMap v) z) := by
  obtain ⟨r, hr⟩ := exists_slopeMap_smooth_retraction v hv
  exact DifferentialGeometry.Topology.injective_fundamentalGroup_map_of_leftInverse
    (slopeContinuousMap v) ⟨r, r.property.continuous⟩ hr z

end Circle
