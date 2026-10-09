import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanInduction

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

def isPrincipalSimplex (K : SimplicialComplex ℝ E) (s : Finset E) : Prop :=
  s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → t = s

def erasePrincipalSimplex (K : SimplicialComplex ℝ E) (s : Finset E)
    (hs : isPrincipalSimplex K s) : SimplicialComplex ℝ E where
  faces := K.faces \ {s}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨K.nonempty_of_mem_faces ht.1, ?_⟩
    intro u hut hu
    refine ⟨K.down_closed ht.1 hut hu, ?_⟩
    intro heq
    have hu_s : u = s := heq
    apply ht.2
    exact hs.2 t ht.1 (hu_s ▸ hut)
  indep := fun ht => K.indep ht.1
  inter_subset_convexHull := fun ht hu => K.inter_subset_convexHull ht.1 hu.1

omit [DecidableEq E] in
theorem erasePrincipalSimplex_faces_subset (K : SimplicialComplex ℝ E) (s : Finset E)
    (hs : isPrincipalSimplex K s) : (erasePrincipalSimplex K s hs).faces ⊆ K.faces := by
  classical
  exact fun _ h => h.1

omit [DecidableEq E] in
theorem erasePrincipalSimplex_finite_faces (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (s : Finset E) (hs : isPrincipalSimplex K s) :
    (erasePrincipalSimplex K s hs).faces.Finite := by
  classical
  exact hK.subset (erasePrincipalSimplex_faces_subset K s hs)

omit [DecidableEq E] in
theorem erasePrincipalSimplex_space_union (K : SimplicialComplex ℝ E) (s : Finset E)
    (hs : isPrincipalSimplex K s) :
    (erasePrincipalSimplex K s hs).space ∪ convexHull ℝ (s : Set E) = K.space := by
  classical
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact K.convexHull_subset_space ht.1 hxt
    · exact K.convexHull_subset_space hs.1 hx
  · intro hx
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
    by_cases hts : t = s
    · exact Or.inr (hts ▸ hxt)
    · exact Or.inl ((erasePrincipalSimplex K s hs).convexHull_subset_space ⟨ht, hts⟩ hxt)

def finiteSimplexBoundary (s : Finset E) : Set E :=
  ⋃ a ∈ s, convexHull ℝ ((s.erase a : Finset E) : Set E)

theorem erasePrincipalSimplex_inter_simplex (K : SimplicialComplex ℝ E) (s : Finset E)
    (hs : isPrincipalSimplex K s) :
    (erasePrincipalSimplex K s hs).space ∩ convexHull ℝ (s : Set E) =
      finiteSimplexBoundary s := by
  classical
  ext x
  constructor
  · rintro ⟨hxK, hxs⟩
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxK
    have hnot : ¬ s ⊆ t := fun hst => ht.2 (hs.2 t ht.1 hst)
    obtain ⟨a, has, hat⟩ := Finset.not_subset.mp hnot
    have hxi := K.inter_subset_convexHull hs.1 ht.1 ⟨hxs, hxt⟩
    refine mem_iUnion₂.mpr ⟨a, has, convexHull_mono ?_ hxi⟩
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun hza => hat (hza ▸ hz.2), hz.1⟩
  · intro hx
    obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp hx
    have hne : (s.erase a).Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hxa
      simp only [Finset.coe_empty, convexHull_empty, notMem_empty] at hxa
    have hface : s.erase a ∈ K.faces := K.down_closed hs.1 (Finset.erase_subset _ _) hne
    have hproper : s.erase a ≠ s := by
      intro he
      have hh : a ∈ s.erase a := he.symm ▸ has
      exact Finset.notMem_erase a s hh
    exact ⟨(erasePrincipalSimplex K s hs).convexHull_subset_space ⟨hface, hproper⟩ hxa,
      convexHull_mono (Finset.erase_subset _ _) hxa⟩

omit [DecidableEq E] in
theorem isPrincipalSimplex_of_uncovered {M : Type*} [MetricSpace M]
    {K H : SimplicialComplex ℝ E} {f : C(K.space, M)} {U : Set M} {q : ℕ}
    (h : engulfingDecomposition K H f U q) {s : Finset E} (hs : s ∈ H.faces)
    (hcard : q ≤ s.card)
    (huncovered : ∃ x : K.space, x.1 ∈ convexHull ℝ (s : Set E) ∧ f x ∉ U) :
    isPrincipalSimplex H s := by
  classical
  exact ⟨hs, h.principal_of_uncovered hcard huncovered⟩

end DifferentialGeometry.Topology.Engulfing
