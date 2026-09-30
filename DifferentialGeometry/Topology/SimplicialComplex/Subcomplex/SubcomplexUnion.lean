import DifferentialGeometry.Topology.SimplicialComplex.Refinement.CommonTriangulation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def subcomplexUnion (K : SimplicialComplex ℝ E) (J : ι → SimplicialComplex ℝ E)
    (hJ : ∀ i, (J i).faces ⊆ K.faces) : SimplicialComplex ℝ E where
  faces := ⋃ i, (J i).faces
  isRelLowerSet_faces := by
    rintro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact ⟨(J i).nonempty_of_mem_faces hi, fun t hts ht => mem_iUnion.mpr
      ⟨i, (J i).down_closed hi hts ht⟩⟩
  indep := by
    rintro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact (J i).indep hi
  inter_subset_convexHull := by
    rintro s t hs ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    exact K.inter_subset_convexHull (hJ i hi) (hJ j hj)

theorem subcomplexUnion_faces_subset (K : SimplicialComplex ℝ E)
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces ⊆ K.faces) :
    (subcomplexUnion K J hJ).faces ⊆ K.faces := by
  intro s hs
  obtain ⟨i, hi⟩ := mem_iUnion.mp hs
  exact hJ i hi

theorem subcomplexUnion_space (K : SimplicialComplex ℝ E)
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces ⊆ K.faces) :
    (subcomplexUnion K J hJ).space = ⋃ i, (J i).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact mem_iUnion.mpr ⟨i, (J i).convexHull_subset_space hi hxs⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hi
    exact (subcomplexUnion K J hJ).convexHull_subset_space (mem_iUnion.mpr ⟨i, hs⟩) hxs

theorem subcomplexUnion_finite_faces [Finite ι] (K : SimplicialComplex ℝ E)
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces ⊆ K.faces)
    (hfinite : ∀ i, (J i).faces.Finite) : (subcomplexUnion K J hJ).faces.Finite :=
  finite_iUnion hfinite

theorem subcomplexUnion_face_card_le (K : SimplicialComplex ℝ E)
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces ⊆ K.faces)
    {d : ℕ} (hd : ∀ i, ∀ s ∈ (J i).faces, s.card ≤ d) :
    ∀ s ∈ (subcomplexUnion K J hJ).faces, s.card ≤ d := by
  intro s hs
  obtain ⟨i, hi⟩ := mem_iUnion.mp hs
  exact hd i s hi

theorem affineIndependent_card_le_of_subset_affineSubspace [FiniteDimensional ℝ E]
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    (P : AffineSubspace ℝ E) (hP : (s : Set E) ⊆ P) :
    s.card ≤ Module.finrank ℝ P.direction + 1 := by
  have hspan : affineSpan ℝ (s : Set E) ≤ P := affineSpan_le.mpr hP
  have hdir := AffineSubspace.direction_le hspan
  have hdim := Submodule.finrank_mono hdir
  have hcard := hs.card_le_finrank_succ
  have hdimeq : Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction =
      Module.finrank ℝ (vectorSpan ℝ (s : Set E)) :=
    congrArg (fun Q : Submodule ℝ E => Module.finrank ℝ Q) (direction_affineSpan ℝ (s : Set E))
  rw [hdimeq] at hdim
  have hrange : range (fun v : s => (v : E)) = (s : Set E) := by
    ext x
    exact ⟨fun ⟨v, hv⟩ => hv ▸ v.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hrank : Module.finrank ℝ (vectorSpan ℝ (range (fun v : s => (v : E)))) =
      Module.finrank ℝ (vectorSpan ℝ (s : Set E)) := by rw [hrange]
  simp only [Fintype.card_coe] at hcard
  rw [hrank] at hcard
  exact hcard.trans (Nat.add_le_add_right hdim 1)

end DifferentialGeometry.Topology.Engulfing
