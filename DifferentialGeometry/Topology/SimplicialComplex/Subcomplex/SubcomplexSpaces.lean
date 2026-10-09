import DifferentialGeometry.Topology.Engulfing.Newman.Protected.NewmanQuotient
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementSupport
import DifferentialGeometry.Topology.Engulfing.Local.Charts.LocalOptimalApproximation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

def isSubcomplexSpace (K : SimplicialComplex ℝ E) (C : Set E) : Prop :=
  ∃ R : SimplicialComplex ℝ E, R.faces ⊆ K.faces ∧ R.space = C

namespace isSubcomplexSpace

variable {K : SimplicialComplex ℝ E} {C D : Set E}

omit [DecidableEq E] in
theorem of_faces_subset {R : SimplicialComplex ℝ E} (h : R.faces ⊆ K.faces) :
    isSubcomplexSpace K R.space := by
  classical
  exact ⟨R, h, rfl⟩

omit [DecidableEq E] in
theorem self (K : SimplicialComplex ℝ E) : isSubcomplexSpace K K.space := by
  classical
  exact ⟨K, subset_rfl, rfl⟩

omit [DecidableEq E] in
theorem empty (K : SimplicialComplex ℝ E) : isSubcomplexSpace K ∅ := by
  classical
  exact ⟨⊥, empty_subset _, SimplicialComplex.space_bot⟩

omit [DecidableEq E] in
theorem subset (h : isSubcomplexSpace K C) : C ⊆ K.space := by
  classical
  obtain ⟨R, hR, rfl⟩ := h
  exact subcomplex_space_subset K R hR

omit [DecidableEq E] in
theorem union (hC : isSubcomplexSpace K C) (hD : isSubcomplexSpace K D) :
    isSubcomplexSpace K (C ∪ D) := by
  classical
  obtain ⟨R, hR, rfl⟩ := hC
  obtain ⟨S, hS, rfl⟩ := hD
  exact ⟨subcomplexPair K R S hR hS, subcomplexPair_faces_subset K R S hR hS,
    subcomplexPair_space K R S hR hS⟩

omit [DecidableEq E] in
theorem inter (hC : isSubcomplexSpace K C) (hD : isSubcomplexSpace K D) :
    isSubcomplexSpace K (C ∩ D) := by
  classical
  obtain ⟨R, hR, rfl⟩ := hC
  obtain ⟨S, hS, rfl⟩ := hD
  exact ⟨R ⊓ S, fun _ h => hR h.1, subcomplex_inf_space K R S hR hS⟩

omit [DecidableEq E] in
theorem iUnion {ι : Type*} {A : ι → Set E} (h : ∀ i, isSubcomplexSpace K (A i)) :
    isSubcomplexSpace K (⋃ i, A i) := by
  classical
  choose R hR hspace using h
  refine ⟨subcomplexUnion K R hR, subcomplexUnion_faces_subset K R hR, ?_⟩
  rw [subcomplexUnion_space]
  simp only [hspace]

omit [DecidableEq E] in
theorem face {s : Finset E} (hs : s ∈ K.faces) :
    isSubcomplexSpace K (convexHull ℝ (s : Set E)) := by
  classical
  refine ⟨vertexRestriction K (convexHull ℝ (s : Set E)), fun _ h => h.1, ?_⟩
  rw [(simplicialRefines.refl K).vertexRestriction_space hs]
  exact inter_eq_right.mpr (K.convexHull_subset_space hs)

omit [DecidableEq E] in
theorem subface {s t : Finset E} (hs : s ∈ K.faces) (ht : t ⊆ s) :
    isSubcomplexSpace K (convexHull ℝ (t : Set E)) := by
  classical
  by_cases hne : t.Nonempty
  · exact face (K.down_closed hs ht hne)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    simpa only [he, Finset.coe_empty, convexHull_empty] using empty K

omit [DecidableEq E] in
theorem skeleton (K : SimplicialComplex ℝ E) (p : ℕ) :
    isSubcomplexSpace K (DifferentialGeometry.Topology.Engulfing.skeleton K p).space := by
  classical
  exact of_faces_subset (fun _ hs => hs.1)

omit [DecidableEq E] in
theorem exists_of_subset_skeleton (h : isSubcomplexSpace K C) {p : ℕ}
    (hCp : C ⊆ (DifferentialGeometry.Topology.Engulfing.skeleton K p).space) :
    ∃ R : SimplicialComplex ℝ E, R.faces ⊆ K.faces ∧ R.space = C ∧
      ∀ s ∈ R.faces, s.card ≤ p + 1 := by
  classical
  obtain ⟨R, hR, hspace⟩ := h
  refine ⟨R, hR, hspace, ?_⟩
  intro s hs
  have hc := hCp (hspace.subset
    (R.convexHull_subset_space hs (s.centroid_mem_convexHull (R.nonempty_of_mem_faces hs))))
  obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hc
  exact (Finset.card_le_card (face_subset_of_centroid_mem K (hR hs) ht.1 hct)).trans ht.2

omit [DecidableEq E] in
theorem refine {P : SimplicialComplex ℝ E} (h : isSubcomplexSpace K C)
    (href : simplicialRefines P K) (hspace : P.space = K.space) : isSubcomplexSpace P C := by
  classical
  obtain ⟨R, hR, rfl⟩ := h
  exact ⟨complexRestriction P R, complexRestriction_faces_subset P R,
    complexRestriction_space_of_refines P K R href hspace hR⟩

omit [DecidableEq E] in
theorem isCompact [FiniteDimensional ℝ E] (h : isSubcomplexSpace K C) (hK : K.faces.Finite) :
    IsCompact C := by
  classical
  obtain ⟨R, hR, rfl⟩ := h
  exact isCompact_space_of_finite_faces R (hK.subset hR)

end isSubcomplexSpace

end DifferentialGeometry.Topology.Engulfing
