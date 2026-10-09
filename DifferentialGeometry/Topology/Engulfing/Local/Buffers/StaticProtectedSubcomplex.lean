import DifferentialGeometry.Topology.Engulfing.Local.Buffers.RawFaceNeighborhood
import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexSpaces

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry

noncomputable section

variable {E F : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
omit [DecidableEq E] in
theorem exists_static_protected_subcomplex
    (K L H D Y : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hHK : H.faces ⊆ K.faces)
    (hDK : D.faces ⊆ K.faces) (hYK : Y.faces ⊆ K.faces) (hYD : Y.space ⊆ D.space)
    (a : E → F) (c : F) {r δ : ℝ}
    (hmesh : ∀ s ∈ K.faces, ∀ x ∈ convexHull ℝ (s : Set E),
      ∀ y ∈ convexHull ℝ (s : Set E), dist (a x) (a y) < δ)
    (B : Set F) (hball : ball c (r + δ) ⊆ B) (hYB : a '' Y.space ⊆ B) :
    ∃ C : SimplicialComplex ℝ E,
      C.faces.Finite ∧ C.faces ⊆ K.faces ∧ Y.faces ⊆ C.faces ∧
      C.space ⊆ D.space ∧ C.space ⊆ L.space ∪ H.space ∪ Y.space ∧
      L.space ∩ D.space ⊆ C.space ∧
      H.space ∩ D.space ∩ a ⁻¹' ball c r ⊆ C.space ∧
      a '' ((C.space \ L.space) ∩ H.space) ⊆ B := by
  classical
  let CL := L ⊓ D
  let CH := simplicialNeighborhood (H ⊓ D) (a ⁻¹' ball c r)
  have hCLK : CL.faces ⊆ K.faces := fun _ hs => hLK hs.1
  have hCHK : CH.faces ⊆ K.faces := fun _ hs => hHK hs.1.1
  have hCLs : CL.space = L.space ∩ D.space := subcomplex_inf_space K L D hLK hDK
  have hHDs : (H ⊓ D).space = H.space ∩ D.space := subcomplex_inf_space K H D hHK hDK
  have hCHs : CH.space ⊆ H.space ∩ D.space := by
    rw [← hHDs]
    exact subcomplex_space_subset (H ⊓ D) CH (simplicialNeighborhood_faces_subset _ _)
  have hCHB : a '' CH.space ⊆ B :=
    (image_simplicialNeighborhood_subset_ball (H ⊓ D) a c
      (fun s hs => hmesh s (hHK hs.1))).trans hball
  let CY := subcomplexPair K CH Y hCHK hYK
  have hCYK : CY.faces ⊆ K.faces := subcomplexPair_faces_subset K CH Y hCHK hYK
  let C := subcomplexPair K CL CY hCLK hCYK
  have hCK : C.faces ⊆ K.faces := subcomplexPair_faces_subset K CL CY hCLK hCYK
  have hCs : C.space = (L.space ∩ D.space) ∪ (CH.space ∪ Y.space) := by
    rw [subcomplexPair_space, hCLs, subcomplexPair_space]
  refine ⟨C, hK.subset hCK, hCK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    change s ∈ (subcomplexPair K CL CY hCLK hCYK).faces
    rw [subcomplexPair_faces]
    apply Or.inr
    change s ∈ (subcomplexPair K CH Y hCHK hYK).faces
    rw [subcomplexPair_faces]
    exact Or.inr hs
  · rw [hCs]
    exact union_subset inter_subset_right (union_subset (hCHs.trans inter_subset_right) hYD)
  · rw [hCs]
    rintro x (hx | hx | hx)
    · exact Or.inl (Or.inl hx.1)
    · exact Or.inl (Or.inr (hCHs hx).1)
    · exact Or.inr hx
  · rw [hCs]
    exact subset_union_left
  · rintro x ⟨hxHD, hxa⟩
    rw [hCs]
    apply Or.inr ∘ Or.inl
    apply chart_preimage_subset_simplicialNeighborhood (H ⊓ D) a c r
    exact ⟨hHDs.symm.subset hxHD, hxa⟩
  · rintro _ ⟨x, ⟨⟨hxC, hxL⟩, hxH⟩, rfl⟩
    rw [hCs] at hxC
    rcases hxC with hx | hx | hx
    · exact (hxL hx.1).elim
    · exact hCHB (mem_image_of_mem a hx)
    · exact hYB (mem_image_of_mem a hx)

end

end DifferentialGeometry.Topology.Engulfing
