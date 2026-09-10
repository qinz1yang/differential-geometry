import DifferentialGeometry.Topology.SimplicialComplex.VertexLinkLocalEuler

set_option autoImplicit false
noncomputable section
open Set Poincare.Homology
open scoped Manifold
namespace Poincare.Topology.SimplicialComplex
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [d : DecidableEq E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E) (hp : {p} ∈ K.faces)
  {M : Type} [TopologicalSpace M] [T1Space M] (e : K.space ≃ₜ M)


theorem faceEulerChar_vertexLink_of_interior {n : ℕ} {H : Type} [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H)
    (hx : I.IsInteriorPoint (e ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩)) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex {p}) = 1 - (-1 : ℤ) ^ n := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let x : K.space := ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩
  have hlink := faceEulerChar_vertexLink_eq_one_sub_local K p hp ℚ
  have hmap := relativeEulerChar_chart (X := TopCat.of K.space) (Y := TopCat.of M)
    e.toOpenPartialHomeomorph x (mem_univ x) ℚ
  change relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ =
    relativeEulerChar (TopCat.of M) ({e x}ᶜ : Set M) ℚ at hmap
  have hlocal := relativeEulerChar_localManifold_interior ℚ I (e x) hx
  change _ = 1 - relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ at hlink
  rw [hmap, hlocal] at hlink
  have hd : (fun a b : E => LinearOrder.toDecidableEq a b) = d := Subsingleton.elim _ _
  exact (congrArg (fun d' : DecidableEq E =>
    faceEulerChar (@link E d' K.toPreAbstractSimplicialComplex {p})) hd).symm.trans hlink


theorem faceEulerChar_vertexLink_of_boundary {n : ℕ} [NeZero n]
    [ChartedSpace (EuclideanHalfSpace n) M]
    (hx : (𝓡∂ n).IsBoundaryPoint (e ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩)) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex {p}) = 1 := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let x : K.space := ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩
  have hlink := faceEulerChar_vertexLink_eq_one_sub_local K p hp ℚ
  have hmap := relativeEulerChar_chart (X := TopCat.of K.space) (Y := TopCat.of M)
    e.toOpenPartialHomeomorph x (mem_univ x) ℚ
  change relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ =
    relativeEulerChar (TopCat.of M) ({e x}ᶜ : Set M) ℚ at hmap
  have hlocal := relativeEulerChar_localManifold_boundary ℚ (e x) hx
  change _ = 1 - relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ at hlink
  rw [hmap, hlocal, sub_zero] at hlink
  have hd : (fun a b : E => LinearOrder.toDecidableEq a b) = d := Subsingleton.elim _ _
  exact (congrArg (fun d' : DecidableEq E =>
    faceEulerChar (@link E d' K.toPreAbstractSimplicialComplex {p})) hd).symm.trans hlink


theorem faceEulerChar_vertexLink_three_interior
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (hx : (𝓡∂ 3).IsInteriorPoint (e ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩)) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex {p}) = 2 := by
  simpa using faceEulerChar_vertexLink_of_interior K p hp e (𝓡∂ 3) hx

end Poincare.Topology.SimplicialComplex
