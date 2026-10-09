/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcCellGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
def trimmedArcCellUnion (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (k : ℕ) : Set E :=
  ⋃ i : Fin k, (derivedNeighborhoodCell K (arcChainFace v (i.val + 1))).space

open Classical in
theorem trimmedArcCellUnion_zero (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) :
    trimmedArcCellUnion K v 0 = ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, -⟩ := mem_iUnion.mp hx
    exact Fin.elim0 i
  · exact fun hx => hx.elim

open Classical in
theorem trimmedArcCellUnion_succ (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (k : ℕ) :
    trimmedArcCellUnion K v (k + 1) =
      trimmedArcCellUnion K v k ∪
        (derivedNeighborhoodCell K (arcChainFace v (k + 1))).space := by
  ext x
  simp only [trimmedArcCellUnion, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hik : i.val = k
    · exact Or.inr ((show i.val + 1 = k + 1 by omega) ▸ hi)
    · let j : Fin k := ⟨i.val, by omega⟩
      exact Or.inl ⟨j, hi⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last k, by simpa using hi⟩

open Classical in
theorem trimmedArcCellUnion_inter_next
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k + 1 ≤ 2 * n) :
    trimmedArcCellUnion K v k ∩
        (derivedNeighborhoodCell K (arcChainFace v (k + 1))).space =
      (derivedNeighborhoodCell K (arcChainFace v k)).space ∩
        (derivedNeighborhoodCell K (arcChainFace v (k + 1))).space := by
  apply Subset.antisymm
  · rintro x ⟨hxU, hxNext⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    by_cases hik : i.val + 1 = k
    · exact ⟨hik ▸ hi, hxNext⟩
    · have hfar : (i.val + 1) + 1 < k + 1 := by
        have hiLt := i.isLt
        omega
      have hdis := disjoint_derivedNeighborhoodCell_arcChainFace hvert hedge hinj
        (i := i.val + 1) (j := k + 1) (by omega) (by omega) hfar
      exact False.elim (Set.disjoint_left.mp hdis hi hxNext)
  · rintro x ⟨hx, hxNext⟩
    let i : Fin k := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by
      dsimp only [i]
      omega
    exact ⟨mem_iUnion.mpr ⟨i, hi.symm ▸ hx⟩, hxNext⟩

open Classical in
theorem trimmedArcCellUnion_inter_next_eq_coneSet
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k + 1 ≤ 2 * n) :
    trimmedArcCellUnion K v k ∩
        (derivedNeighborhoodCell K (arcChainFace v (k + 1))).space =
      coneSet (arcCellCrossing v k) (arcCellInterfaceBase K v k).space := by
  rw [trimmedArcCellUnion_inter_next hvert hedge hinj hk0 hkn,
    adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet
      hvert hedge hinj hkn]

open Classical in
theorem disjoint_trimmedArcCellUnion_next_interface
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    {k : ℕ} (hkn : k + 2 ≤ 2 * n) :
    Disjoint (trimmedArcCellUnion K v k)
      (coneSet (arcCellCrossing v (k + 1))
        (arcCellInterfaceBase K v (k + 1)).space) := by
  rw [← adjacent_derivedNeighborhoodCell_arcChainFace_inter_eq_coneSet
    hvert hedge hinj (j := k + 1) hkn]
  apply Set.disjoint_left.mpr
  intro x hxU hxNext
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
  have hdis := disjoint_derivedNeighborhoodCell_arcChainFace hvert hedge hinj
    (i := i.val + 1) (j := k + 2) (by omega) (by omega) (by omega)
  exact Set.disjoint_left.mp hdis hi hxNext.2

open Classical in
theorem trimmedArcCellUnion_succ_inter_arcComplexIn_space
    (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (n k : ℕ) :
    trimmedArcCellUnion K v (k + 1) ∩ (arcComplexIn K v n).space =
      trimmedArcCellUnion K v k ∩ (arcComplexIn K v n).space ∪
        ((derivedNeighborhoodCell K (arcChainFace v (k + 1))).space ∩
          (arcComplexIn K v n).space) := by
  rw [trimmedArcCellUnion_succ, Set.union_inter_distrib_right]

open Classical in
theorem arcCellCrossing_zero_mem_trimmedArcCellUnion
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k ≤ 2 * n) :
    arcCellCrossing v 0 ∈ trimmedArcCellUnion K v k := by
  have hcross := arcCellCrossing_mem_adjacent_derivedNeighborhoodCells
    hvert hedge hinj (j := 0) (by omega)
  exact mem_iUnion.mpr ⟨⟨0, hk0⟩, hcross.2⟩

open Classical in
theorem arcCellCrossing_mem_trimmedArcCellUnion
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j)
    {k : ℕ} (hk0 : 1 ≤ k) (hkn : k + 1 ≤ 2 * n) :
    arcCellCrossing v k ∈ trimmedArcCellUnion K v k := by
  have hcross := arcCellCrossing_mem_adjacent_derivedNeighborhoodCells
    hvert hedge hinj (j := k) hkn
  let i : Fin k := ⟨k - 1, by omega⟩
  have hi : i.val + 1 = k := by
    dsimp only [i]
    omega
  exact mem_iUnion.mpr ⟨i, hi.symm ▸ hcross.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
