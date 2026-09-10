import DifferentialGeometry.Topology.Manifold.MorseHalfSpaceModel
import DifferentialGeometry.Topology.Manifold.Boundary.GeometricProjectiveObstruction

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Homology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.SimplicialComplex
open scoped Manifold
namespace DifferentialGeometry.Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
  (hLK : L ≤ K) {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (MorseHalfSpace m) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) =
    (morseModelWithCornersHalfSpace m).boundary M)
include hLK e hboundary


theorem eulerChar_morseBoundary_of_geometric_pair (k : Type) [Field k] :
    eulerChar k (TopCat.of ((morseModelWithCornersHalfSpace m).boundary M)) =
      (1 - (-1 : ℤ) ^ (m + 1)) * eulerChar k (TopCat.of M) := by
  let _ := morseHalfSpaceEuclideanChartedSpace m M
  have hb : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ (m + 1)).boundary M :=
    hboundary.trans (morseHalfSpaceEuclidean_boundary m M).symm
  rw [← morseHalfSpaceEuclidean_boundary m M]
  exact eulerChar_boundary_of_geometric_pair hLK e hb k


theorem relativeEulerChar_morseBoundary_of_geometric_pair (k : Type) [Field k] :
    relativeEulerChar (TopCat.of M) ((morseModelWithCornersHalfSpace m).boundary M) k =
      (-1 : ℤ) ^ (m + 1) * eulerChar k (TopCat.of M) := by
  let _ := morseHalfSpaceEuclideanChartedSpace m M
  have hb : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ (m + 1)).boundary M :=
    hboundary.trans (morseHalfSpaceEuclidean_boundary m M).symm
  rw [← morseHalfSpaceEuclidean_boundary m M]
  exact relativeEulerChar_boundary_of_geometric_pair hLK e hb k

end DifferentialGeometry.Manifold

namespace DifferentialGeometry.Manifold
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
  (hLK : L ≤ K) {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (MorseHalfSpace 2) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) =
    (morseModelWithCornersHalfSpace 2).boundary M)
include hLK e hboundary


theorem not_morseBoundary_homeomorphic_projectivePlane_of_geometric_pair :
    ¬Nonempty (((morseModelWithCornersHalfSpace 2).boundary M) ≃ₜ
      Projectivization ℝ (EuclideanSpace ℝ (Fin 3))) := by
  let _ := morseHalfSpaceEuclideanChartedSpace 2 M
  have hb : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ 3).boundary M :=
    hboundary.trans (morseHalfSpaceEuclidean_boundary 2 M).symm
  rintro ⟨f⟩
  apply not_boundary_homeomorphic_projectivePlane_of_geometric_pair hLK e hb
  exact ⟨(Homeomorph.setCongr (morseHalfSpaceEuclidean_boundary 2 M)).trans f⟩

end DifferentialGeometry.Manifold
