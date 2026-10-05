import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure OneStepPrecision (p : CutoffParameters) (B dCap glob : ℝ) where
  precision : ℝ
  order : ℕ
  precision_pos : 0 < precision
  precision_shorter : precision < min (1 / 4) (min (p.delta B) (min dCap glob))
  order_lower : max (p.modelOrder + 6) (2 * ⌊precision⁻¹⌋₊ + 4) ≤ order

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
