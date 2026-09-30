import DifferentialGeometry.Topology.Engulfing.Simplex.SimplexMembrane

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq E] in
private theorem inter_adjoined_simplex (K : SimplicialComplex ℝ E)
    (V B : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (hB : B ∈ K.faces) (hBV : B ⊆ V)
    (hattach : K.space ∩ convexHull ℝ (V : Set E) = convexHull ℝ (B : Set E))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ⊆ V) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ t) := by
  classical
  rintro x ⟨hxs, hxt⟩
  have hxB : x ∈ convexHull ℝ (B : Set E) := hattach ▸
    ⟨K.convexHull_subset_space hs hxs, convexHull_mono ht hxt⟩
  have hxSB := K.inter_subset_convexHull hs hB ⟨hxs, hxB⟩
  have hSB : s ∩ B ⊆ V := (Finset.inter_subset_right).trans hBV
  have hi := AffineIndependent.convexHull_inter (R := ℝ) (s := V) (t₁ := s ∩ B)
    (t₂ := t) hV hSB ht
  have hx : x ∈ convexHull ℝ (((s ∩ B : Finset E) : Set E) ∩ t) :=
    hi.symm ▸ ⟨by simpa only [Finset.coe_inter] using hxSB, hxt⟩
  exact convexHull_mono (show (((s ∩ B : Finset E) : Set E) ∩ (t : Set E)) ⊆
    (s : Set E) ∩ (t : Set E) from fun _ hy => ⟨(Finset.mem_inter.mp hy.1).1, hy.2⟩) hx

def adjoinSimplexAlongFace (K : SimplicialComplex ℝ E)
    (V B : Finset E) (hV : AffineIndependent ℝ ((↑) : V → E))
    (hB : B ∈ K.faces) (hBV : B ⊆ V)
    (hattach : K.space ∩ convexHull ℝ (V : Set E) = convexHull ℝ (B : Set E)) :
    SimplicialComplex ℝ E where
  faces := K.faces ∪ {s | s ⊆ V ∧ s.Nonempty}
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨K.nonempty_of_mem_faces hs, fun t hts ht => Or.inl (K.down_closed hs hts ht)⟩
    · exact ⟨hs.2, fun t hts ht => Or.inr ⟨hts.trans hs.1, ht⟩⟩
  indep := by
    intro s hs
    rcases hs with hs | hs
    · exact K.indep hs
    · exact hV.mono hs.1
  inter_subset_convexHull := by
    intro s t hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact K.inter_subset_convexHull hs ht
    · exact inter_adjoined_simplex K V B hV hB hBV hattach hs ht.1
    · simpa only [inter_comm] using inter_adjoined_simplex K V B hV hB hBV hattach ht hs.1
    · exact (AffineIndependent.convexHull_inter (R := ℝ) hV hs.1 ht.1).symm.subset

namespace AdjoinSimplexAlongFace

variable (K : SimplicialComplex ℝ E) (V B : Finset E)
  (hV : AffineIndependent ℝ ((↑) : V → E)) (hB : B ∈ K.faces) (hBV : B ⊆ V)
  (hattach : K.space ∩ convexHull ℝ (V : Set E) = convexHull ℝ (B : Set E))

omit [DecidableEq E] in
theorem old_faces_subset : K.faces ⊆ (adjoinSimplexAlongFace K V B hV hB hBV hattach).faces := by
  classical
  exact subset_union_left

omit [DecidableEq E] in
theorem simplex_mem_faces : V ∈ (adjoinSimplexAlongFace K V B hV hB hBV hattach).faces := by
  classical
  exact Or.inr ⟨subset_rfl, (K.nonempty_of_mem_faces hB).mono hBV⟩

omit [DecidableEq E] in
theorem finite_faces (hK : K.faces.Finite) :
    (adjoinSimplexAlongFace K V B hV hB hBV hattach).faces.Finite := by
  classical
  exact hK.union ((V.powerset.finite_toSet).subset (fun _ hs => Finset.mem_powerset.mpr hs.1))

omit [DecidableEq E] in
theorem space : (adjoinSimplexAlongFace K V B hV hB hBV hattach).space =
    K.space ∪ convexHull ℝ (V : Set E) := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    rcases hs with hs | hs
    · exact Or.inl (K.convexHull_subset_space hs hxs)
    · exact Or.inr (convexHull_mono hs.1 hxs)
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact SimplicialComplex.mem_space_iff.mpr ⟨s, Or.inl hs, hxs⟩
    · exact SimplicialComplex.mem_space_iff.mpr
        ⟨V, simplex_mem_faces K V B hV hB hBV hattach, hx⟩

omit [DecidableEq E] in
theorem face_card_le {d r : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (hcard : V.card ≤ r + 1) :
    ∀ s ∈ (adjoinSimplexAlongFace K V B hV hB hBV hattach).faces,
      s.card ≤ max d r + 1 := by
  classical
  intro s hs
  rcases hs with hs | hs
  · exact (hd s hs).trans (Nat.add_le_add_right (le_max_left _ _) 1)
  · exact (Finset.card_le_card hs.1).trans
      (hcard.trans (Nat.add_le_add_right (le_max_right _ _) 1))

end AdjoinSimplexAlongFace

end

end DifferentialGeometry.Topology.Engulfing
