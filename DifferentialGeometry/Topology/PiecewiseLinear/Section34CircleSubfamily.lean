import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDeletion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_embedding_of_isPLSphere_one_subfamily {ι κ : Type*} [Finite ι]
    {J : ι → Set E} {C : κ → Set E} (hJ : ∀ i, IsPLSphere 1 (J i))
    (hC : ∀ k, IsPLSphere 1 (C k)) (hJdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hCdis : Pairwise fun i j => Disjoint (C i) (C j))
    (hsub : ∀ k, C k ⊆ ⋃ i, J i) : ∃ a : κ ↪ ι, ∀ k, C k = J (a k) := by
  have hex (k : κ) : ∃ i, C k = J i := by
    obtain ⟨i, hi⟩ := subset_of_isPreconnected_of_iUnion_isClosed
      (fun i => (hJ i).isPolyhedron.isClosed) hJdis (hC k).isConnected.isPreconnected
      (hC k).nonempty (hsub k)
    exact ⟨i, eq_of_subset_of_isPLSphere_one (hC k) (hJ i) hi⟩
  choose a ha using hex
  refine ⟨⟨a, ?_⟩, ha⟩
  intro k l hkl
  by_contra hne
  obtain ⟨x, hx⟩ := (hC k).nonempty
  have heq : C k = C l := (ha k).trans ((congrArg J hkl).trans (ha l).symm)
  exact disjoint_left.mp (hCdis hne) hx (heq ▸ hx)

theorem exists_strict_circle_subfamily_after_local_pair_cancellation
    {ι : Type*} [Finite ι] {J : ι → Set E} {C : Fin 3 → Set E} {S K : Set E}
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hC : ∀ k, IsPLSphere 1 (C k))
    (hJdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hCdis : Pairwise fun i j => Disjoint (C i) (C j))
    (htrace : (⋃ i, J i) ∩ S = ⋃ k, C k) (hKS : K ⊆ S) (hKC : Disjoint K (C 2)) :
    ∃ I : Set ι, I.Nonempty ∧ Nat.card I < Nat.card ι ∧
      (((⋃ i, J i) \ S) ∪ C 2) = ⋃ i : I, J i.1 ∧
      ∀ i : I, Disjoint K (J i.1) := by
  have hCsub (k : Fin 3) : C k ⊆ ⋃ i, J i :=
    (subset_iUnion C k).trans (htrace.symm.subset.trans inter_subset_left)
  obtain ⟨a, ha⟩ := exists_embedding_of_isPLSphere_one_subfamily hJ hC hJdis hCdis hCsub
  let I : Set ι := {i | i ≠ a 0 ∧ i ≠ a 1}
  have h2 : a 2 ∈ I := ⟨fun h => by simpa using a.injective h,
    fun h => by simpa using a.injective h⟩
  have h0 : a 0 ∉ I := fun h => h.1 rfl
  have hcard : Nat.card I < Nat.card ι := Set.ncard_lt_card
    (fun h => h0 (h ▸ mem_univ (a 0)))
  have hindex {i : ι} {k : Fin 3} {x : E} (hx : x ∈ J i) (hxc : x ∈ C k) : i = a k := by
    by_contra hne
    exact disjoint_left.mp (hJdis hne) hx ((ha k).subset hxc)
  have hretained {i : I} {x : E} (hx : x ∈ J i.1) (hxS : x ∈ S) : x ∈ C 2 := by
    obtain ⟨k, hxk⟩ := mem_iUnion.mp (htrace.subset ⟨mem_iUnion.mpr ⟨i.1, hx⟩, hxS⟩)
    have hi := hindex hx hxk
    fin_cases k
    · exact (i.2.1 hi).elim
    · exact (i.2.2 hi).elim
    · exact hxk
  refine ⟨I, ⟨a 2, h2⟩, hcard, Subset.antisymm ?_ ?_, ?_⟩
  · rintro x (⟨hx, hxS⟩ | hx)
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      have hi : i ∈ I := by
        constructor
        · intro hi
          have hxC : x ∈ C 0 := (ha 0).symm ▸ (hi ▸ hxi)
          exact hxS (htrace.superset (mem_iUnion.mpr ⟨0, hxC⟩)).2
        · intro hi
          have hxC : x ∈ C 1 := (ha 1).symm ▸ (hi ▸ hxi)
          exact hxS (htrace.superset (mem_iUnion.mpr ⟨1, hxC⟩)).2
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    · exact mem_iUnion.mpr ⟨⟨a 2, h2⟩, (ha 2).subset hx⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    by_cases hxS : x ∈ S
    · exact Or.inr (hretained hxi hxS)
    · exact Or.inl ⟨mem_iUnion.mpr ⟨i.1, hxi⟩, hxS⟩
  · intro i
    exact disjoint_left.mpr fun x hxK hxi =>
      disjoint_left.mp hKC hxK (hretained hxi (hKS hxK))


theorem exists_strict_circle_subfamily_after_deleting_region
    {ι κ : Type*} [Finite ι] [Nonempty κ] {J : ι → Set E} {C : κ → Set E} {S : Set E}
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hC : ∀ k, IsPLSphere 1 (C k))
    (hJdis : Pairwise fun i j => Disjoint (J i) (J j))
    (hCdis : Pairwise fun i j => Disjoint (C i) (C j))
    (htrace : (⋃ i, J i) ∩ S = ⋃ k, C k) :
    ∃ I : Set ι, Nat.card I < Nat.card ι ∧
      ((⋃ i, J i) \ S) = ⋃ i : I, J i.1 ∧ ∀ i : I, Disjoint S (J i.1) := by
  have hCsub (k : κ) : C k ⊆ ⋃ i, J i :=
    (subset_iUnion C k).trans (htrace.symm.subset.trans inter_subset_left)
  obtain ⟨a, ha⟩ := exists_embedding_of_isPLSphere_one_subfamily hJ hC hJdis hCdis hCsub
  let I : Set ι := (range a)ᶜ
  obtain ⟨k₀⟩ := ‹Nonempty κ›
  have hcard : Nat.card I < Nat.card ι := Set.ncard_lt_card (by
    intro h
    have hm : a k₀ ∈ I := h ▸ mem_univ (a k₀)
    exact hm ⟨k₀, rfl⟩)
  have hkeep (i : I) : Disjoint S (J i.1) := by
    refine disjoint_left.mpr ?_
    intro x hxS hxJ
    obtain ⟨k, hxC⟩ := mem_iUnion.mp (htrace.subset ⟨mem_iUnion.mpr ⟨i.1, hxJ⟩, hxS⟩)
    have hne : i.1 ≠ a k := fun h => i.2 ⟨k, h.symm⟩
    exact disjoint_left.mp (hJdis hne) hxJ ((ha k).subset hxC)
  refine ⟨I, hcard, Subset.antisymm ?_ ?_, hkeep⟩
  · rintro x ⟨hx, hxS⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have hi : i ∈ I := by
      rintro ⟨k, rfl⟩
      have hxC := (ha k).symm.subset hxi
      exact hxS (htrace.superset (mem_iUnion.mpr ⟨k, hxC⟩)).2
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact ⟨mem_iUnion.mpr ⟨i.1, hxi⟩, disjoint_right.mp (hkeep i) hxi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
