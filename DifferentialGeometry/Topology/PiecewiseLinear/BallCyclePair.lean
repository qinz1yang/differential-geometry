import DifferentialGeometry.Topology.PiecewiseLinear.BallChain

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cycleGraph_adj_zero_one {n : ℕ} :
    (SimpleGraph.cycleGraph (n + 3)).Adj 0 1 := by
  apply SimpleGraph.pathGraph_le_cycleGraph
  refine SimpleGraph.pathGraph_adj.mpr (Or.inl ?_)
  simp

theorem cycleGraph_adj_zero_last {n : ℕ} :
    (SimpleGraph.cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
  rw [SimpleGraph.cycleGraph_adj']
  left
  have hlt : (0 : Fin (n + 3)) < Fin.last (n + 2) := by
    simp [Fin.lt_def]
  rw [Fin.coe_sub_iff_lt.mpr hlt]
  simp

theorem not_cycleGraph_adj_zero {n : ℕ} {a : Fin (n + 3)} (h2 : 2 ≤ a.val)
    (hlast : a.val ≤ n + 1) : ¬(SimpleGraph.cycleGraph (n + 3)).Adj 0 a := by
  rw [SimpleGraph.cycleGraph_adj']
  have hlt : (0 : Fin (n + 3)) < a := by
    simp only [Fin.lt_def, Fin.val_zero]
    omega
  have hs₁ : ((0 : Fin (n + 3)) - a).val = n + 3 + (0 : Fin (n + 3)).val - a.val :=
    Fin.coe_sub_iff_lt.mpr hlt
  have hs₂ : (a - (0 : Fin (n + 3))).val = a.val := by
    simp
  rw [hs₁, hs₂]
  simp only [Fin.val_zero]
  omega

theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_succ_of_cycle
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} (C : Fin (n + 3) → Set E)
    (hC : ∀ i, IsPLBall 3 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (C i) (C j)) :
    IsPLBall 3 (⋃ i : Fin (n + 2), C i.succ) := by
  apply hK.isPLBall_iUnion_of_chain (fun i : Fin (n + 2) => C i.succ)
    (fun i => hC i.succ) (fun i => hCK i.succ)
  · intro i
    apply hnext
    apply SimpleGraph.pathGraph_le_cycleGraph
    refine SimpleGraph.pathGraph_adj.mpr (Or.inl ?_)
    simp
  · intro i j hij
    have hlt : i.succ < j.succ := by
      simp only [Fin.lt_def, Fin.val_succ]
      omega
    apply hdis i.succ j.succ (ne_of_lt hlt)
    rw [SimpleGraph.cycleGraph_adj']
    have hs₁ : (i.succ - j.succ).val = n + 3 + i.succ.val - j.succ.val :=
      Fin.coe_sub_iff_lt.mpr hlt
    have hs₂ : (j.succ - i.succ).val = j.succ.val - i.succ.val :=
      Fin.sub_val_of_le hlt.le
    rw [hs₁, hs₂]
    simp only [Fin.val_succ]
    have hj : j.val < n + 2 := j.isLt
    omega

theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_pair_cover_of_cycle
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} (C : Fin (n + 3) → Set E)
    (hC : ∀ i, IsPLBall 3 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (C i) (C j))
    (htriple : ∀ i j l : Fin (n + 3), i ≠ j → i ≠ l → j ≠ l → C i ∩ C j ∩ C l = ∅) :
    ∃ A B D₀ D₁ : Set E, IsPLBall 3 A ∧ IsPLBall 3 B ∧ IsPLBall 2 D₀ ∧ IsPLBall 2 D₁ ∧
      Disjoint D₀ D₁ ∧ A ∪ B = ⋃ i, C i ∧ A ∩ B = D₀ ∪ D₁ := by
  have hone : ((1 : Fin (n + 3))).val = 1 := by
    simp
  have hlastval : (Fin.last (n + 2)).val = n + 2 := rfl
  refine ⟨C 0, ⋃ i : Fin (n + 2), C i.succ, C 0 ∩ C 1, C 0 ∩ C (Fin.last (n + 2)),
    hC 0, hK.isPLBall_iUnion_succ_of_cycle C hC hCK hnext hdis,
    hnext 0 1 cycleGraph_adj_zero_one, hnext 0 _ cycleGraph_adj_zero_last, ?_, ?_, ?_⟩
  · rw [Set.disjoint_iff_inter_eq_empty]
    have hne₁ : (0 : Fin (n + 3)) ≠ 1 := by
      intro h
      rw [Fin.ext_iff, hone] at h
      simp at h
    have hne₂ : (0 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
      intro h
      rw [Fin.ext_iff, hlastval] at h
      simp at h
    have hne₃ : (1 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
      intro h
      rw [Fin.ext_iff, hone, hlastval] at h
      omega
    have htr := htriple 0 1 (Fin.last (n + 2)) hne₁ hne₂ hne₃
    rw [← Set.subset_empty_iff, ← htr]
    intro x hx
    exact ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
  · ext x
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hx | ⟨i, hi⟩)
      · exact ⟨0, hx⟩
      · exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact Or.inl hi
      · exact Or.inr ⟨j, hi⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ⟨hx0, i, hi⟩
      by_cases h1 : i.succ = 1
      · exact Or.inl ⟨hx0, h1 ▸ hi⟩
      · by_cases hl : i.succ = Fin.last (n + 2)
        · exact Or.inr ⟨hx0, hl ▸ hi⟩
        · have h2 : 2 ≤ i.succ.val := by
            have : i.succ.val ≠ 1 := fun h => h1 (Fin.ext (by rw [h, hone]))
            have hpos : 0 < i.succ.val := by
              simp [Fin.val_succ]
            omega
          have hle : i.succ.val ≤ n + 1 := by
            have : i.succ.val ≠ n + 2 := fun h => hl (Fin.ext (by rw [h, hlastval]))
            have := i.succ.isLt
            omega
          have hne : (0 : Fin (n + 3)) ≠ i.succ := by
            intro h
            rw [Fin.ext_iff, Fin.val_zero] at h
            omega
          exact absurd hi (Set.disjoint_left.mp
            (hdis 0 i.succ hne (not_cycleGraph_adj_zero h2 hle)) hx0)
    · rintro (⟨hx0, hx1⟩ | ⟨hx0, hxl⟩)
      · exact ⟨hx0, 0, by simpa using hx1⟩
      · exact ⟨hx0, Fin.last (n + 1), by simpa using hxl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
