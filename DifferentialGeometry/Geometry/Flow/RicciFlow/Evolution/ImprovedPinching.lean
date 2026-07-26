import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.Definitions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.TfHeatCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.Quotient
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.HamiltonRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.TfHeatAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.BookData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.Wrappers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ImprovedPinching.Estimate

/-!
# Improved Ricci pinching quantities

Compatibility umbrella for the split Hamilton Section 10 improved-pinching API.
Public declaration names remain in their original namespaces; downstream
imports of `DifferentialGeometry.PDE.RicciFlow.Evolution.ImprovedPinching` should continue to
work unchanged.
-/
