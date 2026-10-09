import DifferentialGeometry.Topology.Engulfing.Local.Charts.LocalReplacement
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.CommonTriangulation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def simplicialNeighborhood (K : SimplicialComplex ℝ E) (A : Set E) :
    SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ ∃ t ∈ K.faces, s ⊆ t ∧
    (convexHull ℝ (t : Set E) ∩ A).Nonempty}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro u hus hu
    obtain ⟨t, ht, hst, hmeet⟩ := hs.2
    exact ⟨K.down_closed hs.1 hus hu, t, ht, hus.trans hst, hmeet⟩
  indep := fun hs => K.indep hs.1
  inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1

omit [DecidableEq E] in
theorem simplicialNeighborhood_faces_subset (K : SimplicialComplex ℝ E) (A : Set E) :
    (simplicialNeighborhood K A).faces ⊆ K.faces := by
  classical
  exact fun _ h => h.1

omit [DecidableEq E] in
theorem simplicialNeighborhood_finite_faces (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (A : Set E) : (simplicialNeighborhood K A).faces.Finite := by
  classical
  exact hK.subset (simplicialNeighborhood_faces_subset K A)

omit [DecidableEq E] in
theorem subset_simplicialNeighborhood (K : SimplicialComplex ℝ E) (A : Set E) :
    A ∩ K.space ⊆ (simplicialNeighborhood K A).space := by
  classical
  rintro x ⟨hxA, hxK⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hxK
  exact (simplicialNeighborhood K A).convexHull_subset_space
    ⟨hs, s, hs, subset_rfl, x, hxs, hxA⟩ hxs

omit [DecidableEq E] in
theorem simplicialNeighborhood_space_subset (K : SimplicialComplex ℝ E) (A U : Set E)
    (hU : ∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ A).Nonempty →
      convexHull ℝ (s : Set E) ⊆ U) :
    (simplicialNeighborhood K A).space ⊆ U := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, hst, hmeet⟩ := hs.2
  exact hU t ht hmeet (convexHull_mono hst hxs)

omit [DecidableEq E] in
theorem exists_subcomplex_neighborhood_preserving
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    {A U : Set E} (hA : IsCompact A) (hAK : A ⊆ K.space)
    (hU : IsOpen U) (hAU : A ⊆ U) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ P J D : SimplicialComplex ℝ E,
      P.faces.Finite ∧ P.space = K.space ∧ simplicialRefines P K ∧
      (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      J.faces.Finite ∧ J.faces ⊆ P.faces ∧ J.space = L.space ∧ simplicialRefines J L ∧
      D.faces.Finite ∧ D.faces ⊆ P.faces ∧ D.space ⊆ U ∧ A ⊆ D.space ∧
      (Subtype.val ⁻¹' A : Set P.space) ⊆ interior (Subtype.val ⁻¹' D.space) := by
  classical
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA.isClosed hU hAU
  let N := K.space ∩ closure V
  have hN : IsCompact N := (isCompact_space_of_finite_faces K hK).inter_right isClosed_closure
  have hNU : N ⊆ U := fun _ hx => hVU hx.2
  obtain ⟨Q, hQ, hQspace, hQref, hnear⟩ :=
    exists_subdivision_faces_near_compact K hK hN hU hNU
  have hLQ : L.space ⊆ Q.space := by
    rw [hQspace]
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hLK hs) hxs
  obtain ⟨P, J, hP, hPspace, hPref, hPdim, hJ, hJP, hJspace, hJref⟩ :=
    exists_subdivision_containing_complex Q L hQ (hK.subset hLK) hLQ
      (hQref.face_card_le hd)
  let D := simplicialNeighborhood P N
  have hDspace : D.space ⊆ U := by
    apply simplicialNeighborhood_space_subset P N U
    intro s hs hmeet
    obtain ⟨t, ht, hst⟩ := hPref s hs
    apply hst.trans (hnear t ht ?_)
    obtain ⟨x, hxs, hxN⟩ := hmeet
    exact ⟨x, hst hxs, hxN⟩
  refine ⟨P, J, D, hP, hPspace.trans hQspace, hPref.trans hQref, hPdim,
    hJ, hJP, hJspace, hJref, simplicialNeighborhood_finite_faces P hP N,
    simplicialNeighborhood_faces_subset P N, hDspace, ?_, ?_⟩
  · intro x hx
    apply subset_simplicialNeighborhood P N
    exact ⟨⟨hAK hx, subset_closure (hAV hx)⟩, (hPspace.trans hQspace).symm ▸ hAK hx⟩
  · have hVsub : (Subtype.val ⁻¹' V : Set P.space) ⊆ Subtype.val ⁻¹' D.space := by
      intro x hx
      apply subset_simplicialNeighborhood P N
      exact ⟨⟨(hPspace.trans hQspace) ▸ x.2, subset_closure hx⟩, x.2⟩
    exact (preimage_mono hAV).trans
      ((hV.preimage continuous_subtype_val).subset_interior_iff.mpr hVsub)

end DifferentialGeometry.Topology.Engulfing
