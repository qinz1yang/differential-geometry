import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Components
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Pairing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Producers

set_option autoImplicit false

/-!
# Ricci-Flow Connection Evolution in a Fixed Frame

Compatibility umbrella for fixed-frame Ricci-flow connection evolution.
The implementation is split by component, lowered-pairing, raised-Christoffel,
and final producer layers under `DifferentialGeometry.PDE.RicciFlow.Evolution.Connection.*`.
-/
