/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalFiniteEvenAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerStabilization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℕ → ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalTower.exists_displayed_separators_of_stable_rows
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hI : IsOpen I) (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (hX : ∀ n, IsCanonicalSurface (X n) (fun j => φ '' S j) T'' I P' a b)
    (H H' B Jlo Jhi : ℤ → Set E3)
    (hstable : ∀ i n, i.natAbs + 1 ≤ n → (X n i).space = B i)
    (hhalf : ∀ i, IsPLAnnulusWithEnds (H i) (Jhi (i - 1)) (Jlo i) ∧
      IsPLAnnulusWithEnds (H' i) (Jhi (i - 1)) (Jlo i) ∧
      H i ∪ H' i = T'' (2 * i) ∧ H i ∩ H' i = Jhi (i - 1) ∪ Jlo i)
    (hlo : ∀ i, B i ∩ T'' (2 * i) = Jlo i)
    (hhi : ∀ i, B i ∩ T'' (2 * (i + 1)) = Jhi i) :
    ∃ M : ℕ → Set E3,
      M 0 = towerSurface T'' (fun i => (X 0 i).space) P' ∧
      (∀ n, IsSeparatorIn I (M n) {a} {b}) ∧ (∀ n, P' ∈ M n) ∧
      ∀ x ∈ I, x ≠ P' → ∃ U ∈ 𝓝 x, ∃ N : ℕ, ∀ n ≥ N,
        M n ∩ U = annularChain H B P' ∩ U := by
  classical
  let selected (n : ℕ) : Finset ℤ := Finset.Icc (2 - (n : ℤ)) ((n : ℤ) - 1)
  let E (n : ℕ) (j : ℤ) : Set E3 :=
    if j / 2 ∈ selected n then H (j / 2) else T'' j
  have hE (n : ℕ) (i : ℤ) : E n (2 * i) =
      if i ∈ selected n then H i else T'' (2 * i) := by
    simp only [E, show (2 * i) / 2 = i by omega]
  have hHT (i : ℤ) : H i ⊆ T'' (2 * i) :=
    subset_union_left.trans (hhalf i).2.2.1.subset
  have hET (n : ℕ) (i : ℤ) : E n (2 * i) ⊆ T'' (2 * i) := by
    rw [hE]
    split_ifs
    · exact hHT i
    · exact Subset.rfl
  have hmem (n : ℕ) (i : ℤ) (hi : i ∈ selected n) :
      i.natAbs + 1 ≤ n ∧ (i - 1).natAbs + 1 ≤ n := by
    simp only [selected, Finset.mem_Icc] at hi
    rcases Int.natAbs_eq i with habs | habs <;>
      rcases Int.natAbs_eq (i - 1) with hprev | hprev <;> omega
  have hsep (n : ℕ) :
      IsSeparatorIn I (towerSurface (E n) (fun i => (X n i).space) P') {a} {b} := by
    apply (hX n).isSeparatorIn_of_finite_even_annuli htw hI havoid (E n) (selected n)
    · intro i hi
      rw [hE, ite_eq_right hi]
    · intro i hi
      obtain ⟨h₀, h₁⟩ := hmem n i hi
      refine ⟨H' i, Jhi (i - 1), Jlo i, ?_, (hhalf i).2.1, ?_, ?_, ?_, ?_⟩
      · rw [hE, ite_eq_left hi]
        exact (hhalf i).1
      · rw [hE, ite_eq_left hi]
        exact (hhalf i).2.2.1
      · rw [hE, ite_eq_left hi]
        exact (hhalf i).2.2.2
      · rw [hstable (i - 1) n h₁]
        simpa only [sub_add_cancel] using hhi (i - 1)
      · rw [hstable i n h₀]
        exact hlo i
  refine ⟨fun n => towerSurface (E n) (fun i => (X n i).space) P', ?_, hsep,
    fun _ => Or.inr rfl, ?_⟩
  · rfl
  · apply htw.locally_eventually_eq_annularChain hET (fun n i => (hX n).carrier i)
    · intro i
      refine ⟨i.natAbs + (i - 1).natAbs + 2, fun n hn => ?_⟩
      rw [hE, ite_eq_left]
      simp only [selected, Finset.mem_Icc]
      rcases Int.natAbs_eq i with habs | habs <;>
        rcases Int.natAbs_eq (i - 1) with hprev | hprev <;> omega
    · exact fun i => ⟨i.natAbs + 1, hstable i⟩

end DifferentialGeometry.Topology.PiecewiseLinear
