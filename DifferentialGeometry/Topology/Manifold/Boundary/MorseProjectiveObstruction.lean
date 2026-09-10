import DifferentialGeometry.Topology.Manifold.MorseHalfSpaceSmooth
import DifferentialGeometry.Topology.Manifold.Boundary.ProjectiveObstruction

set_option autoImplicit false
noncomputable section
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff
namespace DifferentialGeometry.Manifold

theorem not_morseBoundary_homeomorphic_projectivePlane
    {M : Type} [TopologicalSpace M] [ChartedSpace (MorseHalfSpace 2) M]
    [IsManifold (morseModelWithCornersHalfSpace 2) ∞ M] [T2Space M] [CompactSpace M] :
    ¬Nonempty (((morseModelWithCornersHalfSpace 2).boundary M) ≃ₜ
      Projectivization ℝ (EuclideanSpace ℝ (Fin 3))) := by
  let _ := morseHalfSpaceEuclideanChartedSpace 2 M
  let _ := morseHalfSpaceEuclidean_isManifold 2 M
  rintro ⟨h⟩
  apply not_boundary_homeomorphic_projectivePlane (M := M)
  exact ⟨(Homeomorph.setCongr (morseHalfSpaceEuclidean_boundary 2 M)).trans h⟩

end DifferentialGeometry.Manifold
