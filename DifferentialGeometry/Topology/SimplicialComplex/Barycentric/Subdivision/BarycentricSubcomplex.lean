import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.FineSubdivision

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem barycentricSubdivision_faces_subset {L K : SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) :
    (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces := by
  rintro s ⟨C, hCne, hC, hCL, rfl⟩
  exact ⟨C, hCne, hC, fun t ht => hLK (hCL t ht), rfl⟩

theorem barycentricSubdivisionIter_faces_subset {L K : SimplicialComplex ℝ E}
    (hLK : L.faces ⊆ K.faces) (N : ℕ) :
    (barycentricSubdivisionIter L N).faces ⊆ (barycentricSubdivisionIter K N).faces := by
  induction N with
  | zero => exact hLK
  | succ N ih => exact barycentricSubdivision_faces_subset ih

theorem barycentricSubdivision_faces_union (H R Q : SimplicialComplex ℝ E)
    (hfaces : H.faces = R.faces ∪ Q.faces) :
    (barycentricSubdivision H).faces =
      (barycentricSubdivision R).faces ∪ (barycentricSubdivision Q).faces := by
  ext s
  constructor
  · rintro ⟨C, hCne, hC, hCH, rfl⟩
    obtain ⟨T, hTC, hCT⟩ := hC.exists_largest hCne
    have hT := hCH T hTC
    rw [hfaces] at hT
    rcases hT with hTR | hTQ
    · exact Or.inl ⟨C, hCne, hC,
        fun t ht => R.down_closed hTR (hCT t ht) (hC.1 t ht), rfl⟩
    · exact Or.inr ⟨C, hCne, hC,
        fun t ht => Q.down_closed hTQ (hCT t ht) (hC.1 t ht), rfl⟩
  · intro hs
    rcases hs with hs | hs
    · exact barycentricSubdivision_faces_subset (by rw [hfaces]; exact subset_union_left) hs
    · exact barycentricSubdivision_faces_subset (by rw [hfaces]; exact subset_union_right) hs

theorem barycentricSubdivisionIter_faces_union (H R Q : SimplicialComplex ℝ E)
    (hfaces : H.faces = R.faces ∪ Q.faces) (N : ℕ) :
    (barycentricSubdivisionIter H N).faces =
      (barycentricSubdivisionIter R N).faces ∪ (barycentricSubdivisionIter Q N).faces := by
  induction N with
  | zero => exact hfaces
  | succ N ih => exact barycentricSubdivision_faces_union _ _ _ ih

theorem barycentricSubdivisionIter_face_card_le_nat (K : SimplicialComplex ℝ E)
    {q : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ q) (N : ℕ) :
    ∀ s ∈ (barycentricSubdivisionIter K N).faces, s.card ≤ q := by
  cases q with
  | zero =>
      have hK : K = ⊥ := by
        apply SimplicialComplex.ext
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
        have hz := hd s hs
        omega
      subst K
      have hempty : (barycentricSubdivisionIter (⊥ : SimplicialComplex ℝ E) N).space = ∅ := by
        rw [barycentricSubdivisionIter_space, SimplicialComplex.space_bot]
      intro s hs
      obtain ⟨a, ha⟩ := (barycentricSubdivisionIter (⊥ : SimplicialComplex ℝ E) N).nonempty_of_mem_faces hs
      have hx := (barycentricSubdivisionIter (⊥ : SimplicialComplex ℝ E) N).subset_space hs ha
      rw [hempty] at hx
      exact hx.elim
  | succ q => exact barycentricSubdivisionIter_face_card_le K hd N

end DifferentialGeometry.Topology.Engulfing
