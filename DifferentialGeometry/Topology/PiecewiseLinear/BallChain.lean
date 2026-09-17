import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_of_chain
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} (C : Fin (n + 1) → Set E)
    (hC : ∀ i, IsPLBall 3 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i : Fin n, IsPLBall 2 (C i.castSucc ∩ C i.succ))
    (hfar : ∀ i j, i.val + 1 < j.val → Disjoint (C i) (C j)) :
    IsPLBall 3 (⋃ i, C i) := by
  induction n with
  | zero =>
    have hu : (⋃ i, C i) = C 0 := by
      ext x
      simp only [mem_iUnion]
      exact ⟨fun ⟨i, hi⟩ => (show i = 0 from Fin.ext (by omega)) ▸ hi, fun hi => ⟨0, hi⟩⟩
    exact hu.symm ▸ hC 0
  | succ n ih =>
    let P : Fin (n + 1) → Set E := fun i => C i.castSucc
    have hP : IsPLBall 3 (⋃ i, P i) := ih P (fun i => hC i.castSucc)
      (fun i => hCK i.castSucc) (fun i => hnext i.castSucc)
      (fun i j hij => hfar i.castSucc j.castSucc hij)
    have hPK : (⋃ i, P i) ⊆ K.space := iUnion_subset fun i => hCK i.castSucc
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
    have hball : IsPLBall 3 ((⋃ i, P i) ∪ C (Fin.last (n + 1))) :=
      hK.isPLBall_union_of_inter_isPLBall_two hP (hC (Fin.last (n + 1)))
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

theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_castSucc_of_cycle
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} (C : Fin (n + 3) → Set E)
    (hC : ∀ i, IsPLBall 3 (C i)) (hCK : ∀ i, C i ⊆ K.space)
    (hnext : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (C i ∩ C j))
    (hdis : ∀ i j, i ≠ j → ¬(SimpleGraph.cycleGraph (n + 3)).Adj i j → Disjoint (C i) (C j)) :
    IsPLBall 3 (⋃ i : Fin (n + 2), C i.castSucc) := by
  apply hK.isPLBall_iUnion_of_chain (fun i => C i.castSucc)
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
end DifferentialGeometry.Topology.PiecewiseLinear
