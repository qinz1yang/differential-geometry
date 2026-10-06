import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGraphThresholdUL
import DifferentialGeometry.Geometry.Collapse.GraphManifold

/-!
# Consumer of `a01_boundary_univ_UL` (lane S-ULIFT, G3)

The boundary endpoint input at EVERY universe has the type of the admitted
`exists_boundary_graph_threshold.{u}`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.GraphManifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The admitted statement `exists_boundary_graph_threshold.{u}`, proved. -/
example (K : ℕ) (hK : staticDerivativeOrder ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :=
  (a01_boundary_univ_UL.{u} K hK A hA :
    type_of% (exists_boundary_graph_threshold.{u} K hK A hA))

end DifferentialGeometry.Geometry.Collapse
