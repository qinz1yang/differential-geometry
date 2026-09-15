import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_isSubdivision_subcomplexes_closedStars_subset_openStar [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J : Type*} [Finite J] (Q : J → Set E) (hQ : ∀ j, IsPolyhedron (Q j))
    (hQK : ∀ j, Q j ⊆ K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      (∀ j, (restrict R (Q j)).space = Q j) ∧
      ∀ s ∈ R.faces, ∃ v ∈ K.vertices, (⋃ w ∈ s, closedStar R w) ⊆ openStar K v := by
  have hcover : K.space ⊆ ⋃ v : K.vertices, openStar K v := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := exists_vertex_mem_openStar K hx
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, hxv⟩
  obtain ⟨R, hR, hfinite, hQR, hstars⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover K Q hQ hQK
      (fun v : K.vertices => openStar K v) (fun v => isOpen_preimage_openStar K v) hcover
  exact ⟨R, hR, hfinite, hQR, fun s hs => by
    obtain ⟨v, hv⟩ := hstars s hs
    exact ⟨v, v.property, hv⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
