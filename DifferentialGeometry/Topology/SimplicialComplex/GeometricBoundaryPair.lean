import DifferentialGeometry.Topology.SimplicialComplex.GeometricManifoldLinks
import DifferentialGeometry.Topology.SimplicialComplex.GeometricManifoldFaceLinks
import DifferentialGeometry.Topology.SimplicialComplex.BoundaryCounting

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold
namespace DifferentialGeometry.Topology.SimplicialComplex
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} (hLK : L ≤ K)
include hLK


theorem singleton_mem_subcomplex_iff_mem_space {p : E} (hp : {p} ∈ K.faces) :
    {p} ∈ L.faces ↔ p ∈ L.space := by
  constructor
  · intro h
    exact Geometry.SimplicialComplex.vertices_subset_space (K := L) h
  · intro h
    obtain ⟨s, hs, hpS⟩ := Geometry.SimplicialComplex.mem_space_iff.mp h
    exact L.down_closed hs
      (Finset.singleton_subset_iff.mpr ((K.vertex_mem_convexHull_iff hp (hLK hs)).mp hpS))
      (Finset.singleton_nonempty p)

section Boundary
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ n).boundary M)
include hboundary

omit hLK in
theorem geometricSubcomplex_mem_boundary_iff (x : K.space) :
    x.val ∈ L.space ↔ (𝓡∂ n).IsBoundaryPoint (e x) := by
  constructor
  · intro h
    change e x ∈ (𝓡∂ n).boundary M
    rw [← hboundary]
    exact ⟨x, h, rfl⟩
  · intro h
    change e x ∈ (𝓡∂ n).boundary M at h
    rw [← hboundary] at h
    obtain ⟨y, hy, he⟩ := h
    have he' := e.injective he
    exact he' ▸ hy


theorem singleton_mem_subcomplex_iff_boundary {p : E} (hp : {p} ∈ K.faces) :
    {p} ∈ L.faces ↔ (𝓡∂ n).IsBoundaryPoint
      (e ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩) :=
  (singleton_mem_subcomplex_iff_mem_space hLK hp).trans
    (geometricSubcomplex_mem_boundary_iff e hboundary
      ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩)


theorem face_mem_subcomplex_iff_boundary {s : Finset E} (hs : s ∈ K.faces) :
    s ∈ L.faces ↔ (𝓡∂ n).IsBoundaryPoint (e (geometricFaceBarycenter K s hs)) :=
  (geometricFaceBarycenter_mem_subcomplex_iff K s hs L hLK).symm.trans
    (geometricSubcomplex_mem_boundary_iff e hboundary (geometricFaceBarycenter K s hs))

open Classical in
theorem faceLink_values_of_geometric_boundary [DecidableEq E] [Finite K.faces] [T1Space M]
    {s : Finset E} (hs : s ∈ K.faces) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) =
      if s ∈ L.faces then 1 else 1 - (-1 : ℤ) ^ (s.card - 1) * (-1 : ℤ) ^ n := by
  classical
  have hpoint := face_mem_subcomplex_iff_boundary hLK e hboundary hs
  by_cases hL : s ∈ L.faces
  · rw [if_pos hL]
    exact faceEulerChar_faceLink_of_boundary K s hs e (hpoint.mp hL)
  · rw [if_neg hL]
    apply faceEulerChar_faceLink_of_interior K s hs e (𝓡∂ n)
    rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
    exact fun h => hL (hpoint.mpr h)

end Boundary

section Three
variable [DecidableEq E] [Finite K.faces]
  {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace (EuclideanHalfSpace 3) M]
  (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ 3).boundary M)
include hboundary

open Classical in
theorem vertexLink_values_of_geometric_boundary {s : Finset E}
    (hs : s ∈ facesOfCard K.toPreAbstractSimplicialComplex 1) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) = if s ∈ L.faces then 1 else 2 := by
  classical
  have hcard := (mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard.2
  have hp : {p} ∈ K.faces := hcard.1
  have hpoint := singleton_mem_subcomplex_iff_boundary hLK e hboundary hp
  by_cases hL : {p} ∈ L.faces
  · rw [if_pos hL]
    exact faceEulerChar_vertexLink_of_boundary K p hp e (hpoint.mp hL)
  · rw [if_neg hL]
    apply faceEulerChar_vertexLink_three_interior K p hp e
    rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
    exact fun h => hL (hpoint.mpr h)

omit [DecidableEq E] in
theorem card_boundary_vertices_of_geometric_manifold [Finite L.faces]
    (hd : ∀ s ∈ K.faces, s.card ≤ 4) :
    ((facesOfCard L.toPreAbstractSimplicialComplex 1).card : ℤ) =
      2 * (facesOfCard K.toPreAbstractSimplicialComplex 1).card -
        2 * (facesOfCard K.toPreAbstractSimplicialComplex 2).card +
          3 * (facesOfCard K.toPreAbstractSimplicialComplex 3).card -
            4 * (facesOfCard K.toPreAbstractSimplicialComplex 4).card := by
  classical
  exact card_boundary_vertices K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex
    hLK hd (fun _ hs => vertexLink_values_of_geometric_boundary hLK e hboundary hs)

end Three
end DifferentialGeometry.Topology.SimplicialComplex
