import DifferentialGeometry.Topology.Simplex.SupportFace
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

noncomputable section

namespace DifferentialGeometry.Simplex

variable (ι : Type*) [Fintype ι]

def skeleton (k : ℕ) : Set (stdSimplex ℝ ι) :=
  {p | ∃ s : Finset ι, s.card ≤ k + 1 ∧ p ∈ supportFace s}

variable {ι}

theorem skeleton_mono {k l : ℕ} (h : k ≤ l) : skeleton ι k ⊆ skeleton ι l := by
  rintro p ⟨s, hs, hp⟩
  exact ⟨s, hs.trans (Nat.add_le_add_right h 1), hp⟩

theorem supportFace_subset_skeleton {k : ℕ} {s : Finset ι} (h : s.card ≤ k + 1) :
    supportFace s ⊆ skeleton ι k := fun _ hp ↦ ⟨s, h, hp⟩

theorem isClosed_skeleton (k : ℕ) : IsClosed (skeleton ι k) := by
  classical
  have h : skeleton ι k = ⋃ s : {s : Finset ι // s.card ≤ k + 1}, supportFace s.val := by
    ext p
    simp only [skeleton, Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [h]
  exact isClosed_iUnion_of_finite fun s ↦ isClosed_supportFace s.val

theorem mem_skeleton_of_zero_coordinate {k : ℕ} {s : Finset ι}
    (hs : s.card ≤ k + 2) {p : stdSimplex ℝ ι} (hp : p ∈ supportFace s)
    {i : ι} (hi : i ∈ s) (hpi : p i = 0) : p ∈ skeleton ι k := by
  classical
  refine ⟨s.erase i, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hi]
    omega
  · intro j hj
    by_cases hji : j = i
    · simpa [hji] using hpi
    · exact hp j (fun hjs ↦ hj (Finset.mem_erase.mpr ⟨hji, hjs⟩))

theorem supportFaceRestrict_mem_boundary_iff_mem_skeleton {k : ℕ} {s : Finset ι}
    (hs : s.card = k + 2) (p : supportFace s) :
    supportFaceRestrict s p ∈ boundary s ↔ p.val ∈ skeleton ι k := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    exact mem_skeleton_of_zero_coordinate hs.le p.property i.property hi
  · rintro ⟨r, hr, hp⟩
    have hnot : ¬ s ⊆ r := by
      intro h
      have hc := Finset.card_le_card h
      omega
    obtain ⟨i, his, hir⟩ := Finset.not_subset.mp hnot
    exact ⟨⟨i, his⟩, hp i hir⟩

theorem supportFace_inter_subset_skeleton {k : ℕ} {s t : Finset ι}
    (hs : s.card = k + 2) (ht : t.card = k + 2) (hne : s ≠ t) :
    supportFace s ∩ supportFace t ⊆ skeleton ι k := by
  classical
  rintro p ⟨hps, hpt⟩
  have hnot : ¬ s ⊆ t := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h (by omega))
  obtain ⟨i, his, hit⟩ := Finset.not_subset.mp hnot
  exact mem_skeleton_of_zero_coordinate hs.le hps his (hpt i hit)

theorem skeleton_succ_eq_union (k : ℕ) :
    skeleton ι (k + 1) = skeleton ι k ∪
      ⋃ s : {s : Finset ι // s.card = k + 2}, supportFace s.val := by
  ext p
  constructor
  · rintro ⟨s, hs, hp⟩
    by_cases h : s.card ≤ k + 1
    · exact Or.inl ⟨s, h, hp⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨s, by omega⟩, hp⟩)
  · rintro (hp | hp)
    · exact skeleton_mono (Nat.le_succ k) hp
    · obtain ⟨s, hp⟩ := Set.mem_iUnion.mp hp
      exact ⟨s.val, by omega, hp⟩

theorem skeleton_eq_univ {k : ℕ} (h : Fintype.card ι ≤ k + 1) :
    skeleton ι k = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro p
  refine ⟨Finset.univ, ?_, ?_⟩
  · simpa using h
  · intro i hi
    exact (hi (Finset.mem_univ i)).elim

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Simplex

variable {ι : Type*} [Fintype ι]

theorem mem_skeleton_iff_exists_supportFace_card_eq {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι) {p : stdSimplex ℝ ι} :
    p ∈ skeleton ι k ↔ ∃ s : Finset ι, s.card = k + 1 ∧ p ∈ supportFace s := by
  constructor
  · intro hp
    obtain ⟨s, hs, hp⟩ := hp
    obtain ⟨t, hst, ht⟩ := Finset.exists_superset_card_eq hs hk
    exact ⟨t, ht, supportFace_mono hst hp⟩
  · rintro ⟨s, hs, hp⟩
    exact supportFace_subset_skeleton hs.le hp

theorem skeleton_eq_iUnion_supportFace_card_eq {k : ℕ}
    (hk : k + 1 ≤ Fintype.card ι) :
    skeleton ι k = ⋃ s : {s : Finset ι // s.card = k + 1}, supportFace s.val := by
  ext p
  rw [mem_skeleton_iff_exists_supportFace_card_eq hk]
  simp only [Set.mem_iUnion, Subtype.exists, exists_prop]

end DifferentialGeometry.Simplex
