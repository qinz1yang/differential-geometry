import DifferentialGeometry.Topology.Manifold.MorseHalfSpaceModel
import DifferentialGeometry.Topology.Manifold.SmoothModelTransport

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff
namespace Poincare.Manifold

theorem morseHalfSpaceEuclidean_isManifold (m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (MorseHalfSpace m) M] [IsManifold (morseModelWithCornersHalfSpace m) ∞ M] :
    let _ := morseHalfSpaceEuclideanChartedSpace m M
    IsManifold (𝓡∂ (m + 1)) ∞ M :=
  isManifold_transHomeomorph (morseModelWithCornersHalfSpace m) (𝓡∂ (m + 1))
    (morseHalfSpaceHomeomorphism m) (morseEuclideanCoordinates m)
    (morseHalfSpaceHomeomorphism_model m)

end Poincare.Manifold
