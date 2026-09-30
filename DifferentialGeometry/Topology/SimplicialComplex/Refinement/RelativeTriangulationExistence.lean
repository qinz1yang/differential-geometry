import DifferentialGeometry.Topology.SimplicialComplex.Expansion.PrincipalFaces
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.CommonTriangulation
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Card

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def geometricComplexesCompatible (K L : SimplicialComplex ℝ E) : Prop :=
  ∀ s ∈ K.faces, ∀ t ∈ L.faces,
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E))

theorem geometricComplexesCompatible.symm {K L : SimplicialComplex ℝ E}
    (h : geometricComplexesCompatible K L) : geometricComplexesCompatible L K := by
  intro s hs t ht
  simpa only [inter_comm] using h t ht s hs

def geometricComplexUnion (K L : SimplicialComplex ℝ E)
    (h : geometricComplexesCompatible K L) : SimplicialComplex ℝ E where
  faces := K.faces ∪ L.faces
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with hs | hs
    · exact ⟨K.nonempty_of_mem_faces hs,
        fun t hts ht => Or.inl (K.down_closed hs hts ht)⟩
    · exact ⟨L.nonempty_of_mem_faces hs,
        fun t hts ht => Or.inr (L.down_closed hs hts ht)⟩
  indep := fun hs => hs.elim K.indep L.indep
  inter_subset_convexHull := by
    intro s t hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact K.inter_subset_convexHull hs ht
    · exact h s hs t ht
    · exact h.symm s hs t ht
    · exact L.inter_subset_convexHull hs ht

theorem geometricComplexUnion_left (K L : SimplicialComplex ℝ E)
    (h : geometricComplexesCompatible K L) :
    K.faces ⊆ (geometricComplexUnion K L h).faces := subset_union_left

theorem geometricComplexUnion_right (K L : SimplicialComplex ℝ E)
    (h : geometricComplexesCompatible K L) :
    L.faces ⊆ (geometricComplexUnion K L h).faces := subset_union_right

theorem geometricComplexUnion_space (K L : SimplicialComplex ℝ E)
    (h : geometricComplexesCompatible K L) :
    (geometricComplexUnion K L h).space = K.space ∪ L.space := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp hx
    rcases hs with hs | hs
    · exact Or.inl (K.convexHull_subset_space hs hx)
    · exact Or.inr (L.convexHull_subset_space hs hx)
  · rintro (hx | hx)
    · obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact (geometricComplexUnion K L h).convexHull_subset_space (Or.inl hs) hx
    · obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact (geometricComplexUnion K L h).convexHull_subset_space (Or.inr hs) hx

theorem geometricComplexUnion_finite (K L : SimplicialComplex ℝ E)
    (h : geometricComplexesCompatible K L) (hK : K.faces.Finite) (hL : L.faces.Finite) :
    (geometricComplexUnion K L h).faces.Finite := hK.union hL

theorem geometricComplexUnion_card_le (K L : SimplicialComplex ℝ E)
    (h : geometricComplexesCompatible K L) {d : ℕ}
    (hK : ∀ s ∈ K.faces, s.card ≤ d) (hL : ∀ s ∈ L.faces, s.card ≤ d) :
    ∀ s ∈ (geometricComplexUnion K L h).faces, s.card ≤ d := by
  intro s hs
  exact hs.elim (hK s) (hL s)

theorem geometricComplexUnion_refines (K L Q : SimplicialComplex ℝ E)
    (h : geometricComplexesCompatible K L)
    (hK : simplicialRefines K Q) (hL : simplicialRefines L Q) :
    simplicialRefines (geometricComplexUnion K L h) Q := by
  intro s hs
  exact hs.elim (hK s) (hL s)

theorem geometricComplexesCompatible_of_face_inter_space
    (K L : SimplicialComplex ℝ E)
    (hmeet : ∀ s ∈ L.faces, ∃ t : Finset E, t ⊆ s ∧
      (t ∈ K.faces ∨ t = ∅) ∧
      convexHull ℝ (s : Set E) ∩ K.space = convexHull ℝ (t : Set E)) :
    geometricComplexesCompatible K L := by
  intro u hu s hs x hx
  obtain ⟨t, hts, ht, hmeet⟩ := hmeet s hs
  have hxt : x ∈ convexHull ℝ (t : Set E) := by
    rw [← hmeet]
    exact ⟨hx.2, K.convexHull_subset_space hu hx.1⟩
  rcases ht with ht | rfl
  · exact convexHull_mono (show (u : Set E) ∩ (t : Set E) ⊆
        (u : Set E) ∩ (s : Set E) from fun y hy => ⟨hy.1, hts hy.2⟩)
      (K.inter_subset_convexHull hu ht ⟨hx.1, hxt⟩)
  · simp only [Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hxt

theorem geometricComplexesCompatible_of_boundary_faces
    (K L B : SimplicialComplex ℝ E) {S boundary : Set E}
    (hLS : L.space ⊆ S) (hKS : K.space ∩ S ⊆ boundary)
    (hBK : B.faces ⊆ K.faces)
    (hboundary : ∀ s ∈ L.faces, ∃ t : Finset E, t ⊆ s ∧
      (t ∈ B.faces ∨ t = ∅) ∧
      convexHull ℝ (s : Set E) ∩ boundary = convexHull ℝ (t : Set E)) :
    geometricComplexesCompatible K L := by
  apply geometricComplexesCompatible_of_face_inter_space K L
  intro s hs
  obtain ⟨t, hts, ht, hface⟩ := hboundary s hs
  refine ⟨t, hts, ht.imp (fun ht => hBK ht) id, Subset.antisymm ?_ ?_⟩
  · intro x hx
    rw [← hface]
    exact ⟨hx.1, hKS ⟨hx.2, hLS (L.convexHull_subset_space hs hx.1)⟩⟩
  · intro x hx
    refine ⟨convexHull_mono hts hx, ?_⟩
    rcases ht with ht | rfl
    · exact K.convexHull_subset_space (hBK ht) hx
    · simp only [Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hx

variable [DecidableEq E]

omit [DecidableEq E] in
theorem exists_principalSimplex_outside_subcomplex
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hLK : L.faces ⊆ K.faces) (hne : K ≠ L) :
    ∃ s : Finset E, isPrincipalSimplex K s ∧ s ∉ L.faces := by
  classical
  have hnonempty : (K.faces \ L.faces).Nonempty := by
    by_contra hn
    have hKL : K.faces ⊆ L.faces := by
      intro s hs
      by_contra hsl
      exact hn ⟨s, hs, hsl⟩
    exact hne (SimplicialComplex.ext (Subset.antisymm hKL hLK))
  obtain ⟨s, hs, hmax⟩ := (hK.sdiff (t := L.faces)).exists_maximal hnonempty
  refine ⟨s, ⟨hs.1, ?_⟩, hs.2⟩
  intro t ht hst
  have htl : t ∉ L.faces := by
    intro htl
    exact hs.2 (L.down_closed htl hst (K.nonempty_of_mem_faces hs.1))
  exact Finset.Subset.antisymm (hmax ⟨ht, htl⟩ hst) hst

omit [DecidableEq E] in
theorem finite_complex_relative_induction
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (P : SimplicialComplex ℝ E → Prop) (hbase : P L)
    (hstep : ∀ Q : SimplicialComplex ℝ E, Q.faces ⊆ K.faces → L.faces ⊆ Q.faces →
      ∀ (s : Finset E) (hs : isPrincipalSimplex Q s), s ∉ L.faces →
        P (erasePrincipalSimplex Q s hs) → P Q) : P K := by
  classical
  have hrec : ∀ m : ℕ, ∀ Q : SimplicialComplex ℝ E,
      Q.faces ⊆ K.faces → L.faces ⊆ Q.faces → Q.faces.ncard = m → P Q := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro Q hQK hLQ hm
      by_cases hQL : Q = L
      · exact hQL ▸ hbase
      · obtain ⟨s, hs, hsL⟩ :=
          exists_principalSimplex_outside_subcomplex Q L (hK.subset hQK) hLQ hQL
        have hdel : (erasePrincipalSimplex Q s hs).faces ⊂ Q.faces := by
          refine ⟨erasePrincipalSimplex_faces_subset Q s hs, ?_⟩
          intro hreverse
          exact (hreverse hs.1).2 rfl
        have hlt : (erasePrincipalSimplex Q s hs).faces.ncard < m := by
          rw [← hm]
          exact Set.ncard_lt_ncard hdel (hK.subset hQK)
        apply hstep Q hQK hLQ s hs hsL
        apply ih _ hlt _
          ((erasePrincipalSimplex_faces_subset Q s hs).trans hQK) ?_ rfl
        intro t ht
        refine ⟨hLQ ht, ?_⟩
        intro hts
        exact hsL (hts ▸ ht)
  exact hrec K.faces.ncard K subset_rfl hLK rfl

end

end DifferentialGeometry.Topology.Engulfing
