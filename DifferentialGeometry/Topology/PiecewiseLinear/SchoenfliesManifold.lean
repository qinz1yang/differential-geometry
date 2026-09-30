import DifferentialGeometry.Topology.PiecewiseLinear.ChartBallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SimplyEmbedded

open Set
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [HasGroupoid X (plGroupoid 3)]

theorem exists_isPolyhedralBall_of_isPolyhedralSphere_in_chart
    {S : Set X} (hS : IsPolyhedralSphere (n := 3) 2 S)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin 3)) X) (hconv : Convex ℝ e.target) (hSe : S ⊆ e.source) :
    ∃ C : Set X, IsPolyhedralBall (n := 3) 3 C ∧ frontier C = S ∧ C ⊆ e.source := by
  have himage : IsPLSphere 2 (e '' S) := hS.isPLSphere_chart_image e he hSe
  have hSt : e '' S ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hSe hx)
  obtain ⟨B, hB, hfront, hBt⟩ := exists_hasPushProperty_subset_of_isSimplyEmbedded
    himage.isSimplyEmbedded hconv e.open_target hSt
  refine ⟨e.symm '' B, isPolyhedralBall_chart_symm_image e he hB.1 hBt, ?_, ?_⟩
  · rw [frontier_chart_symm_image_of_isPLBall e he hB.1 hBt, hfront]
    exact e.symm_image_image_of_subset_source hSe
  · rintro _ ⟨x, hx, rfl⟩
    exact e.map_target (hBt hx)

theorem exists_isPolyhedralBall_of_isPolyhedralSphere_in_openStar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K)
    {p : E} (hp : {p} ∈ K.faces) :
    letI := combinatorialChartedSpace K hK
    ∀ {S : Set K.space}, IsPolyhedralSphere (n := 3) 2 S → S ⊆ Subtype.val ⁻¹' openStar K p →
      ∃ C : Set K.space, IsPolyhedralBall (n := 3) 3 C ∧ frontier C = S ∧
        C ⊆ Subtype.val ⁻¹' openStar K p := by
  let _ := combinatorialChartedSpace K hK
  let _ := combinatorialChartedSpace_hasGroupoid K hK
  intro S hS hSe
  let e := vertexChart K hp (hK.isPLSphere_link hp)
  have he : e ∈ atlas (EuclideanSpace ℝ (Fin 3)) K.space := ⟨⟨p, hp⟩, rfl⟩
  exact exists_isPolyhedralBall_of_isPolyhedralSphere_in_chart hS e he (convex_stdTarget 2) hSe

end DifferentialGeometry.Topology.PiecewiseLinear
