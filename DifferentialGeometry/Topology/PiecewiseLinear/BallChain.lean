/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Ball Chain. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem isPLBall_iUnion_of_chain_of_union
    {d : ℕ} {S : Set E}
    (hunion : ∀ {A B : Set E}, IsPLBall (d + 1) A → IsPLBall (d + 1) B →
      A ⊆ S → B ⊆ S → IsPLBall d (A ∩ B) → IsPLBall (d + 1) (A ∪ B))
    {n : ℕ} (C : Fin (n + 1) → Set E)
    (hC : ∀ i, IsPLBall (d + 1) (C i)) (hCK : ∀ i, C i ⊆ S)
    (hnext : ∀ i : Fin n, IsPLBall d (C i.castSucc ∩ C i.succ))
    (hfar : ∀ i j, i.val + 1 < j.val → Disjoint (C i) (C j)) :
    IsPLBall (d + 1) (⋃ i, C i) := by
  induction n with
  | zero =>
    have hu : (⋃ i, C i) = C 0 := by
      ext x
      simp only [mem_iUnion]
      exact ⟨fun ⟨i, hi⟩ => (show i = 0 from Fin.ext (by omega)) ▸ hi, fun hi => ⟨0, hi⟩⟩
    exact hu.symm ▸ hC 0
  | succ n ih =>
    let P : Fin (n + 1) → Set E := fun i => C i.castSucc
    have hP : IsPLBall (d + 1) (⋃ i, P i) := ih P (fun i => hC i.castSucc)
      (fun i => hCK i.castSucc) (fun i => hnext i.castSucc)
      (fun i j hij => hfar i.castSucc j.castSucc hij)
    have hPK : (⋃ i, P i) ⊆ S := iUnion_subset fun i => hCK i.castSucc
    have hinter : (⋃ i, P i) ∩ C (Fin.last (n + 1)) =
        C (Fin.last n).castSucc ∩ C (Fin.last (n + 1)) := by
      apply Subset.antisymm
      · rintro x ⟨hxP, hxl⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
        by_cases hil : i = Fin.last n
        · subst i
          exact ⟨hi, hxl⟩
        · have hlt : i.val + 1 < (Fin.last (n + 1)).val := by
            have hne : i.val ≠ n := fun heq => hil (Fin.ext heq)
            simp only [Fin.val_last]
            omega
          exact False.elim (disjoint_left.mp (hfar i.castSucc (Fin.last (n + 1)) hlt) hi hxl)
      · rintro x ⟨hx, hxl⟩
        exact ⟨mem_iUnion.mpr ⟨Fin.last n, hx⟩, hxl⟩
    have hball : IsPLBall (d + 1) ((⋃ i, P i) ∪ C (Fin.last (n + 1))) :=
      hunion hP (hC (Fin.last (n + 1)))
        hPK (hCK (Fin.last (n + 1))) (hinter.symm ▸ hnext (Fin.last n))
    convert hball using 1
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hil : i.val = n + 1
      · exact Or.inr ((Fin.ext hil : i = Fin.last (n + 1)) ▸ hi)
      · let j : Fin (n + 1) := ⟨i.val, by omega⟩
        exact Or.inl ⟨j, show x ∈ C j.castSucc from (show i = j.castSucc from Fin.ext rfl) ▸ hi⟩
    · rintro (⟨i, hi⟩ | hi)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n + 1), hi⟩

omit [FiniteDimensional ℝ E] in
private theorem isPLBall_iUnion_castSucc_of_cycle_of_union
    {d : ℕ} {S : Set E}
    (hunion : ∀ {A B : Set E}, IsPLBall (d + 1) A → IsPLBall (d + 1) B →
      A ⊆ S → B ⊆ S → IsPLBall d (A ∩ B) → IsPLBall (d + 1) (A ∪ B))
    {n : ℕ} (C : Fin (n + 3) → Set E)
    (hC : ∀ i, IsPLBall (d + 1) (C i)) (hCK : ∀ i, C i ⊆ S)
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall d (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j → Disjoint (C i) (C j)) :
    IsPLBall (d + 1) (⋃ i : Fin (n + 2), C i.castSucc) := by
  apply isPLBall_iUnion_of_chain_of_union hunion (fun i => C i.castSucc)
    (fun i => hC i.castSucc) (fun i => hCK i.castSucc)
  · intro i
    apply hnext
    apply SimpleGraph.pathGraph_le_cycleGraph
    exact SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
  · intro i j hij
    have hlt : i.castSucc < j.castSucc := by
      change i.val < j.val
      omega
    apply hdis i.castSucc j.castSucc (ne_of_lt hlt)
    rw [SimpleGraph.cycleGraph_adj']
    have hs₁ : (i.castSucc - j.castSucc).val = n + 3 + i.val - j.val :=
      Fin.coe_sub_iff_lt.mpr hlt
    have hs₂ : (j.castSucc - i.castSucc).val = j.val - i.val :=
      Fin.sub_val_of_le hlt.le
    rw [hs₁, hs₂]
    omega

theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_of_chain
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} (C : Fin (n + 1) → Set E)
    (hC : ∀ i, IsPLBall 3 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i : Fin n, IsPLBall 2 (C i.castSucc ∩ C i.succ))
    (hfar : ∀ i j, i.val + 1 < j.val → Disjoint (C i) (C j)) :
    IsPLBall 3 (⋃ i, C i) :=
  isPLBall_iUnion_of_chain_of_union hK.isPLBall_union_of_inter_isPLBall_two
    C hC hCK hnext hfar

theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_castSucc_of_cycle
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} (C : Fin (n + 3) → Set E)
    (hC : ∀ i, IsPLBall 3 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j → Disjoint (C i) (C j)) :
    IsPLBall 3 (⋃ i : Fin (n + 2), C i.castSucc) :=
  isPLBall_iUnion_castSucc_of_cycle_of_union hK.isPLBall_union_of_inter_isPLBall_two
    C hC hCK hnext hdis

theorem IsCombinatorialManifoldWithBoundary.isPLBall_two_iUnion_of_chain
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {n : ℕ} (C : Fin (n + 1) → Set E)
    (hC : ∀ i, IsPLBall 2 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i : Fin n, IsPLBall 1 (C i.castSucc ∩ C i.succ))
    (hfar : ∀ i j, i.val + 1 < j.val → Disjoint (C i) (C j)) :
    IsPLBall 2 (⋃ i, C i) :=
  isPLBall_iUnion_of_chain_of_union hK.isPLBall_union_of_inter_isPLBall_one
    C hC hCK hnext hfar

theorem IsCombinatorialManifoldWithBoundary.isPLBall_two_iUnion_castSucc_of_cycle
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {n : ℕ} (C : Fin (n + 3) → Set E)
    (hC : ∀ i, IsPLBall 2 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 1 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j → Disjoint (C i) (C j)) :
    IsPLBall 2 (⋃ i : Fin (n + 2), C i.castSucc) :=
  isPLBall_iUnion_castSucc_of_cycle_of_union hK.isPLBall_union_of_inter_isPLBall_one
    C hC hCK hnext hdis

end DifferentialGeometry.Topology.PiecewiseLinear
