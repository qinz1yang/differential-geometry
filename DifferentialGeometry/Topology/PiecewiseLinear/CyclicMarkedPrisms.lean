/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedPrismGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_prism_biUnion_of_marked_chain
    {P : Set E} (hP : IsPolyhedron P) {p : E} (hp : p ∈ P)
    {C : ℕ → Set F} {ρ : ℕ → E × ℝ → F} (n : ℕ)
    (hρ : ∀ i ≤ n, IsPLHomeomorphOn (ρ i) (P ×ˢ Icc (0 : ℝ) 1) (C i))
    (hcap : ∀ i < n, ρ i '' (P ×ˢ {(1 : ℝ)}) = ρ (i + 1) '' (P ×ˢ {(0 : ℝ)}))
    (hmeet : ∀ i < n, C i ∩ C (i + 1) = ρ i '' (P ×ˢ {(1 : ℝ)}))
    (hfar : ∀ i j, j ≤ n → i + 1 < j → Disjoint (C i) (C j))
    (hmark : ∀ i < n, ρ i (p, 1) = ρ (i + 1) (p, 0)) :
    ∃ f : E × ℝ → F,
      IsPLHomeomorphOn f (P ×ˢ Icc (0 : ℝ) 1) (⋃ i ∈ Finset.range (n + 1), C i) ∧
      (∀ x ∈ P, f (x, 0) = ρ 0 (x, 0)) ∧
      f '' (P ×ˢ {(1 : ℝ)}) = ρ n '' (P ×ˢ {(1 : ℝ)}) ∧
      f (p, 1) = ρ n (p, 1) ∧
      f '' ({p} ×ˢ Icc (0 : ℝ) 1) =
        ⋃ i ∈ Finset.range (n + 1), ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  induction n with
  | zero =>
    refine ⟨ρ 0, ?_, fun _ _ => rfl, rfl, rfl, ?_⟩
    · simpa using hρ 0 le_rfl
    · simp
  | succ n ih =>
    obtain ⟨f, hf, hf₀, hf₁, hfp, hfaxis⟩ := ih (fun i hi => hρ i (by omega))
      (fun i hi => hcap i (by omega)) (fun i hi => hmeet i (by omega))
      (fun i j hj hij => hfar i j (by omega) hij) (fun i hi => hmark i (by omega))
    have hinter : (⋃ i ∈ Finset.range (n + 1), C i) ∩ C (n + 1) =
        f '' (P ×ˢ {(1 : ℝ)}) := by
      rw [hf₁, iUnion₂_inter]
      apply Subset.antisymm
      · refine iUnion₂_subset fun i hi => ?_
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        by_cases hin : i = n
        · rw [hin, hmeet n (by omega)]
        · rw [(hfar i (n + 1) le_rfl (by omega)).inter_eq]
          exact empty_subset _
      · intro y hy
        exact mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by omega),
          (hmeet n (by omega)).symm ▸ hy⟩
    obtain ⟨g, hg, hg₀, hg₁, hgp, hgaxis⟩ :=
      exists_isPLHomeomorphOn_prism_union_of_marked_cap hP hf (hρ (n + 1) le_rfl)
        (hf₁.trans (hcap n (by omega))) hinter hp (hfp.trans (hmark n (by omega)))
    refine ⟨g, ?_, fun x hx => (hg₀ x hx).trans (hf₀ x hx), hg₁, hgp, ?_⟩
    · rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
      exact hg
    · rw [Finset.range_add_one, Finset.set_biUnion_insert, union_comm, hgaxis, hfaxis]

theorem exists_cylindricalDiagram_biUnion_of_marked_cycle
    {P : Set E} (hP : IsPolyhedron P) {p : E} (hp : p ∈ P)
    {C : ℕ → Set F} {ρ : ℕ → E × ℝ → F} (n : ℕ)
    (hρ : ∀ i ≤ n + 2, IsPLHomeomorphOn (ρ i) (P ×ˢ Icc (0 : ℝ) 1) (C i))
    (hcap : ∀ i < n + 2,
      ρ i '' (P ×ˢ {(1 : ℝ)}) = ρ (i + 1) '' (P ×ˢ {(0 : ℝ)}))
    (hmeet : ∀ i < n + 2, C i ∩ C (i + 1) = ρ i '' (P ×ˢ {(1 : ℝ)}))
    (hclose : ρ (n + 2) '' (P ×ˢ {(1 : ℝ)}) = ρ 0 '' (P ×ˢ {(0 : ℝ)}))
    (hlast : C 0 ∩ C (n + 2) = ρ 0 '' (P ×ˢ {(0 : ℝ)}))
    (hfar : ∀ i j, j ≤ n + 2 → i + 1 < j →
      (i, j) ≠ (0, n + 2) → Disjoint (C i) (C j))
    (hmark : ∀ i < n + 2, ρ i (p, 1) = ρ (i + 1) (p, 0))
    (hclosed : ρ (n + 2) (p, 1) = ρ 0 (p, 0)) :
    ∃ f : E × ℝ → F, IsCylindricalDiagram f P (⋃ i ∈ Finset.range (n + 3), C i) ∧
      f (p, 0) = f (p, 1) ∧ f '' ({p} ×ˢ Icc (0 : ℝ) 1) =
        ⋃ i ∈ Finset.range (n + 3), ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨f, hf, hf₀, hf₁, hfp, hfaxis⟩ :=
    exists_isPLHomeomorphOn_prism_biUnion_of_marked_chain hP hp (n + 1)
      (fun i hi => hρ i (by omega)) (fun i hi => hcap i (by omega))
      (fun i hi => hmeet i (by omega))
      (fun i j hj hij => hfar i j (by omega) hij
        (fun h => by simp only [Prod.mk.injEq] at h; omega))
      (fun i hi => hmark i (by omega))
  have hf₀' : f '' (P ×ˢ {(0 : ℝ)}) = ρ 0 '' (P ×ˢ {(0 : ℝ)}) := by
    apply image_congr
    rintro ⟨x, t⟩ ⟨hx, rfl⟩
    exact hf₀ x hx
  have hinter : (⋃ i ∈ Finset.range (n + 2), C i) ∩ C (n + 2) =
      f '' (P ×ˢ {(0 : ℝ)}) ∪ f '' (P ×ˢ {(1 : ℝ)}) := by
    rw [hf₀', hf₁, iUnion₂_inter]
    apply Subset.antisymm
    · refine iUnion₂_subset fun i hi => ?_
      have hi' : i < n + 2 := Finset.mem_range.mp hi
      by_cases hi0 : i = 0
      · rw [hi0, hlast]
        exact subset_union_left
      by_cases hin : i = n + 1
      · rw [hin, hmeet (n + 1) (by omega)]
        exact subset_union_right
      · rw [(hfar i (n + 2) le_rfl (by omega)
          (fun h => by simp only [Prod.mk.injEq] at h; omega)).inter_eq]
        exact empty_subset _
    · intro y hy
      rcases hy with hy | hy
      · exact mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr (by omega), hlast.symm ▸ hy⟩
      · exact mem_iUnion₂.mpr ⟨n + 1, Finset.mem_range.mpr (by omega),
          (hmeet (n + 1) (by omega)).symm ▸ hy⟩
  obtain ⟨g, hg, hgclosed, hgaxis⟩ := exists_cylindricalDiagram_of_marked_prism_pair hP hf
    (hρ (n + 2) le_rfl) (hf₁.trans (hcap (n + 1) (by omega)))
    (hclose.trans hf₀'.symm) hinter hp (hfp.trans (hmark (n + 1) (by omega)))
    (hclosed.trans (hf₀ p hp).symm)
  refine ⟨g, ?_, hgclosed, ?_⟩
  · rw [show n + 3 = (n + 2) + 1 by omega,
      Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    exact hg
  · rw [show n + 3 = (n + 2) + 1 by omega,
      Finset.range_add_one, Finset.set_biUnion_insert, union_comm, hgaxis, hfaxis]

open Fin.NatCast in
theorem exists_cylindricalDiagram_iUnion_of_marked_cycle
    {P : Set E} (hP : IsPolyhedron P) {p : E} (hp : p ∈ P)
    (n : ℕ) (C : Fin (n + 3) → Set F) (ρ : Fin (n + 3) → E × ℝ → F)
    (hρ : ∀ i, IsPLHomeomorphOn (ρ i) (P ×ˢ Icc (0 : ℝ) 1) (C i))
    (hmeet : ∀ i, C i ∩ C (i + 1) = ρ i '' (P ×ˢ {(1 : ℝ)}))
    (hcap : ∀ i, ρ i '' (P ×ˢ {(1 : ℝ)}) = ρ (i + 1) '' (P ×ˢ {(0 : ℝ)}))
    (hfar : ∀ i j, i ≠ j → j ≠ i + 1 → i ≠ j + 1 → Disjoint (C i) (C j))
    (hmark : ∀ i, ρ i (p, 1) = ρ (i + 1) (p, 0)) :
    ∃ f : E × ℝ → F, IsCylindricalDiagram f P (⋃ i, C i) ∧
      f (p, 0) = f (p, 1) ∧
      f '' ({p} ×ˢ Icc (0 : ℝ) 1) = ⋃ i, ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1) := by
  let e : ℕ → Fin (n + 3) := fun i => (i : Fin (n + 3))
  have he (i : ℕ) (hi : i < n + 3) : (e i).val = i := Nat.mod_eq_of_lt hi
  have hsucc (i : ℕ) : e (i + 1) = e i + 1 := by simp only [e, Nat.cast_add, Nat.cast_one]
  have hend : e (n + 2) + 1 = e 0 := by
    calc
      e (n + 2) + 1 = e (n + 2 + 1) := (hsucc _).symm
      _ = e (n + 3) := congrArg e (by omega)
      _ = e 0 := by simp only [e, Fin.natCast_self, Nat.cast_zero]
  have hfar' (i j : ℕ) (hj : j ≤ n + 2) (hij : i + 1 < j)
      (hnot : (i, j) ≠ (0, n + 2)) : Disjoint (C (e i)) (C (e j)) := by
    have hi : i < n + 3 := by omega
    have hj' : j < n + 3 := by omega
    apply hfar
    · intro h
      have hv := congrArg Fin.val h
      rw [he i hi, he j hj'] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      rw [← hsucc, he j hj', he (i + 1) (by omega)] at hv
      omega
    · intro h
      by_cases hjlast : j = n + 2
      · subst j
        rw [hend] at h
        have hv := congrArg Fin.val h
        rw [he i hi, he 0 (by omega)] at hv
        exact hnot (Prod.ext hv rfl)
      · have hv := congrArg Fin.val h
        rw [← hsucc, he i hi, he (j + 1) (by omega)] at hv
        omega
  obtain ⟨f, hf, hfclosed, hfaxis⟩ := exists_cylindricalDiagram_biUnion_of_marked_cycle
    hP hp (C := fun i => C (e i)) (ρ := fun i => ρ (e i)) n
    (fun i _ => hρ (e i))
    (fun i _ => by simpa only [hsucc] using hcap (e i))
    (fun i _ => by simpa only [hsucc] using hmeet (e i))
    (by simpa only [hend] using hcap (e (n + 2)))
    (by rw [inter_comm]; simpa only [hend] using
      (hmeet (e (n + 2))).trans (hcap (e (n + 2))))
    hfar' (fun i _ => by simpa only [hsucc] using hmark (e i))
    (by simpa only [hend] using hmark (e (n + 2)))
  have hcover (A : Fin (n + 3) → Set F) :
      (⋃ i ∈ Finset.range (n + 3), A (e i)) = ⋃ i, A i := by
    apply Subset.antisymm
    · exact iUnion₂_subset fun i _ => subset_iUnion A (e i)
    · refine iUnion_subset fun i x hx => ?_
      have hei : e i.val = i := Fin.ext (he i.val i.isLt)
      exact mem_iUnion₂.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, hei.symm ▸ hx⟩
  exact ⟨f, hcover C ▸ hf, hfclosed,
    hfaxis.trans (hcover (fun i => ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1)))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
