/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Combinatorics.StableUnion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.locally_eventually_eq_annularChain
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {E L : ℕ → ℤ → Set E3} {H B : ℤ → Set E3}
    (hE : ∀ n i, E n (2 * i) ⊆ T'' (2 * i))
    (hL : ∀ n i, L n i ⊆ (φ '' S (2 * i) ∪ φ '' S (2 * i + 1)) ∪
      φ '' S (2 * (i + 1)))
    (hEstable : ∀ i, ∃ N : ℕ, ∀ n ≥ N, E n (2 * i) = H i)
    (hLstable : ∀ i, ∃ N : ℕ, ∀ n ≥ N, L n i = B i) :
    ∀ x ∈ I, x ≠ P' → ∃ U ∈ 𝓝 x, ∃ N : ℕ, ∀ n ≥ N,
      towerSurface (E n) (L n) P' ∩ U = annularChain H B P' ∩ U := by
  let R : ℤ → Set E3 := fun i =>
    (φ '' S (2 * i) ∪ φ '' S (2 * i + 1)) ∪ φ '' S (2 * (i + 1))
  have hsupport (n : ℕ) (i : ℤ) : E n (2 * i) ∪ L n i ⊆ R i :=
    union_subset ((hE n i).trans ((htw.boundary_subset_outer _).trans
      (subset_union_left.trans subset_union_left))) (hL n i)
  have hstable (i : ℤ) : ∃ N : ℕ, ∀ n ≥ N, E n (2 * i) ∪ L n i = H i ∪ B i := by
    obtain ⟨N₀, h₀⟩ := hEstable i
    obtain ⟨N₁, h₁⟩ := hLstable i
    exact ⟨max N₀ N₁, fun n hn => by
      rw [h₀ n ((le_max_left _ _).trans hn), h₁ n ((le_max_right _ _).trans hn)]⟩
  intro x hx hxP
  obtain ⟨U, hU, hfinite⟩ := htw.locallyFinite x hx hxP
  have hfinite₀ : {i : ℤ | (φ '' S (2 * i) ∩ U).Nonempty}.Finite :=
    hfinite.preimage (f := fun i : ℤ => 2 * i) (by
      intro a _ b _ hab
      change 2 * a = 2 * b at hab
      omega)
  have hfinite₁ : {i : ℤ | (φ '' S (2 * i + 1) ∩ U).Nonempty}.Finite :=
    hfinite.preimage (f := fun i : ℤ => 2 * i + 1) (by
      intro a _ b _ hab
      change 2 * a + 1 = 2 * b + 1 at hab
      omega)
  have hfinite₂ : {i : ℤ | (φ '' S (2 * (i + 1)) ∩ U).Nonempty}.Finite :=
    hfinite.preimage (f := fun i : ℤ => 2 * (i + 1)) (by
      intro a _ b _ hab
      change 2 * (a + 1) = 2 * (b + 1) at hab
      omega)
  have hrowfinite : {i | (R i ∩ U).Nonempty}.Finite := by
    apply ((hfinite₀.union hfinite₁).union hfinite₂).subset
    rintro i ⟨y, hy, hyU⟩
    rcases hy with (hy₀ | hy₁) | hy₂
    · exact Or.inl (Or.inl ⟨y, hy₀, hyU⟩)
    · exact Or.inl (Or.inr ⟨y, hy₁, hyU⟩)
    · exact Or.inr ⟨y, hy₂, hyU⟩
  obtain ⟨N, hN⟩ := Set.exists_iUnion_inter_eq_of_eventually_eq hsupport hstable hrowfinite
  refine ⟨U, hU, N, ?_⟩
  intro n hn
  simpa only [towerSurface, annularChain, union_inter_distrib_right] using
    congrArg (fun Q : Set E3 => Q ∪ ({P'} ∩ U)) (hN n hn)

end DifferentialGeometry.Topology.PiecewiseLinear
