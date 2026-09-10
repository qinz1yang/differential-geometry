import DifferentialGeometry.Topology.SimplicialComplex.GeometricBoundaryFormula
import DifferentialGeometry.Topology.ProjectiveSpace.EulerCharacteristic

set_option autoImplicit false
noncomputable section
open Set Poincare.Homology Poincare.Topology.SimplicialComplex
open scoped Manifold
namespace Poincare.Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
  (hLK : L ≤ K) {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanHalfSpace 3) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ 3).boundary M)
include hLK e hboundary


theorem not_boundary_homeomorphic_projectivePlane_of_geometric_pair :
    ¬Nonempty (((𝓡∂ 3).boundary M) ≃ₜ
      Projectivization ℝ (EuclideanSpace ℝ (Fin 3))) := by
  rintro ⟨b⟩
  have hboundaryEuler := eulerChar_boundary_of_geometric_pair hLK e hboundary ℚ
  have hRP := eulerChar_eq_of_homeomorph ℚ
    (X := TopCat.of ((𝓡∂ 3).boundary M))
    (Y := TopCat.of (Projectivization ℝ (EuclideanSpace ℝ (Fin 3)))) b
  rw [Poincare.ProjectiveSpace.eulerChar_projectivePlane] at hRP
  norm_num at hboundaryEuler
  omega

end Poincare.Manifold
