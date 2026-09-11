import DifferentialGeometry.Topology.SimplicialComplex.FaceLinkLocalEuler

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Homology
open scoped Manifold
namespace DifferentialGeometry.Topology.SimplicialComplex
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [d : DecidableEq E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (s : Finset E) (hs : s ∈ K.faces)
  {M : Type} [TopologicalSpace M] [T1Space M] (e : K.space ≃ₜ M)


theorem faceEulerChar_faceLink_of_interior {n : ℕ} {H : Type} [TopologicalSpace H]
    [ChartedSpace H M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H)
    (hx : I.IsInteriorPoint (e (geometricFaceBarycenter K s hs))) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) = 1 - (-1 : ℤ) ^ (s.card - 1) * (-1 : ℤ) ^ n := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let x : K.space := geometricFaceBarycenter K s hs
  have hlink := faceEulerChar_link_eq_one_sub_signed_local K s hs ℚ
  have hmap := relativeEulerChar_chart (X := TopCat.of K.space) (Y := TopCat.of M)
    e.toOpenPartialHomeomorph x (mem_univ x) ℚ
  change relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ =
    relativeEulerChar (TopCat.of M) ({e x}ᶜ : Set M) ℚ at hmap
  have hlocal := relativeEulerChar_localManifold_interior ℚ I (e x) hx
  change _ = 1 - (-1 : ℤ) ^ (s.card - 1) * relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ at hlink
  rw [hmap, hlocal] at hlink
  have hd : (fun a b : E => LinearOrder.toDecidableEq a b) = d := Subsingleton.elim _ _
  exact (congrArg (fun d' : DecidableEq E =>
    faceEulerChar (@link E d' K.toPreAbstractSimplicialComplex s)) hd).symm.trans hlink


theorem faceEulerChar_faceLink_of_boundary {n : ℕ} [NeZero n]
    [ChartedSpace (EuclideanHalfSpace n) M]
    (hx : (𝓡∂ n).IsBoundaryPoint (e (geometricFaceBarycenter K s hs))) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) = 1 := by
  classical
  let := linearOrderOfSTO (WellOrderingRel : E → E → Prop)
  let x : K.space := geometricFaceBarycenter K s hs
  have hlink := faceEulerChar_link_eq_one_sub_signed_local K s hs ℚ
  have hmap := relativeEulerChar_chart (X := TopCat.of K.space) (Y := TopCat.of M)
    e.toOpenPartialHomeomorph x (mem_univ x) ℚ
  change relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ =
    relativeEulerChar (TopCat.of M) ({e x}ᶜ : Set M) ℚ at hmap
  have hlocal := relativeEulerChar_localManifold_boundary ℚ (e x) hx
  change _ = 1 - (-1 : ℤ) ^ (s.card - 1) * relativeEulerChar (TopCat.of K.space) ({x}ᶜ : Set K.space) ℚ at hlink
  rw [hmap, hlocal, mul_zero, sub_zero] at hlink
  have hd : (fun a b : E => LinearOrder.toDecidableEq a b) = d := Subsingleton.elim _ _
  exact (congrArg (fun d' : DecidableEq E =>
    faceEulerChar (@link E d' K.toPreAbstractSimplicialComplex s)) hd).symm.trans hlink


theorem faceEulerChar_edgeLink_three_interior
    [ChartedSpace (EuclideanHalfSpace 3) M] (hcard : s.card = 2)
    (hx : (𝓡∂ 3).IsInteriorPoint (e (geometricFaceBarycenter K s hs))) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) = 0 := by
  have h := faceEulerChar_faceLink_of_interior K s hs e (𝓡∂ 3) hx
  norm_num [hcard] at h ⊢
  exact h


theorem faceEulerChar_triangleLink_three_interior
    [ChartedSpace (EuclideanHalfSpace 3) M] (hcard : s.card = 3)
    (hx : (𝓡∂ 3).IsInteriorPoint (e (geometricFaceBarycenter K s hs))) :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) = 2 := by
  have h := faceEulerChar_faceLink_of_interior K s hs e (𝓡∂ 3) hx
  norm_num [hcard] at h ⊢
  exact h

end DifferentialGeometry.Topology.SimplicialComplex
