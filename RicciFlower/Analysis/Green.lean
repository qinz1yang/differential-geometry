import RicciFlower.Analysis.Measure

set_option autoImplicit false

namespace RicciFlower
namespace Analysis
namespace Green

/-!
This module is intentionally no longer a wrapper around the old
`DifferentialGeometry.Integral.DivergenceTheorem.Green` prototype.

That prototype tree now lives locally under `DGreference/` and is ignored by
git.  Future Green/integration-by-parts statements should be rebuilt using the
RicciFlower-local volume, gradient, divergence, and Laplacian interfaces before
this module is exported again from `RicciFlower.lean`.
-/

/-- Marker for the RicciFlower-native Green identity extraction frontier. -/
def localExtractionFrontier : Prop := True

theorem localExtractionFrontier_trivial : localExtractionFrontier := trivial

end Green
end Analysis
end RicciFlower
