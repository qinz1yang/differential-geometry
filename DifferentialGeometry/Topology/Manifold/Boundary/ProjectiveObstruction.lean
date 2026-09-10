import DifferentialGeometry.Topology.Homology.BoundaryEulerIndex
import DifferentialGeometry.Topology.ProjectiveSpace.EulerCharacteristic

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Homology
open scoped Manifold ContDiff
namespace DifferentialGeometry.Manifold

theorem not_boundary_homeomorphic_projectivePlane
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M] :
    ¬Nonempty (((𝓡∂ 3).boundary M) ≃ₜ
      Projectivization ℝ (EuclideanSpace ℝ (Fin 3))) := by
  rintro ⟨b⟩
  have hboundaryEuler := eulerChar_intrinsicBoundary_eq_of_dimension_ge_two (d := 1) (M := M) ℚ
  have hRP := eulerChar_eq_of_homeomorph ℚ
    (X := TopCat.of ((𝓡∂ 3).boundary M))
    (Y := TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) b
  rw [DifferentialGeometry.ProjectiveSpace.eulerChar_projectivePlane] at hRP
  norm_num at hboundaryEuler
  omega

end DifferentialGeometry.Manifold
