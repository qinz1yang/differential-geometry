/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalEvenAnnulusReplacement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.isSeparatorIn_of_finite_even_annuli
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hI : IsOpen I) (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (E : ℤ → Set E3) (selected : Finset ℤ)
    (houtside : ∀ k, k ∉ selected → E (2 * k) = T'' (2 * k))
    (hann : ∀ k ∈ selected, ∃ B J₀ J₁ : Set E3,
      IsPLAnnulusWithEnds (E (2 * k)) J₀ J₁ ∧ IsPLAnnulusWithEnds B J₀ J₁ ∧
      E (2 * k) ∪ B = T'' (2 * k) ∧ E (2 * k) ∩ B = J₀ ∪ J₁ ∧
      (X (k - 1)).space ∩ T'' (2 * k) = J₀ ∧ (X k).space ∩ T'' (2 * k) = J₁) :
    IsSeparatorIn I (towerSurface E (fun j => (X j).space) P') {a} {b} := by
  classical
  induction selected using Finset.induction_on generalizing E with
  | empty =>
    have hsurface : towerSurface E (fun j => (X j).space) P' =
        towerSurface T'' (fun j => (X j).space) P' := by
      unfold towerSurface
      congr 1
      apply iUnion_congr
      intro j
      rw [houtside j (by simp)]
    exact hsurface.symm ▸ hX.separator
  | @insert k s hks ih =>
    obtain ⟨B, J₀, J₁, hA, hB, hcover, hmeet, hleft, hright⟩ := hann k (by simp)
    let E₀ := Function.update E (2 * k) (T'' (2 * k))
    have hother (j : ℤ) (hjk : j ≠ k) : E₀ (2 * j) = E (2 * j) :=
      Function.update_of_ne (by omega : 2 * j ≠ 2 * k) _ _
    have houtside₀ : ∀ j, j ∉ s → E₀ (2 * j) = T'' (2 * j) := by
      intro j hj
      by_cases hjk : j = k
      · subst j
        exact Function.update_self _ _ _
      · rw [hother j hjk]
        exact houtside j (by simp only [Finset.mem_insert]; tauto)
    have hann₀ : ∀ j ∈ s, ∃ B J₀ J₁ : Set E3,
        IsPLAnnulusWithEnds (E₀ (2 * j)) J₀ J₁ ∧ IsPLAnnulusWithEnds B J₀ J₁ ∧
        E₀ (2 * j) ∪ B = T'' (2 * j) ∧ E₀ (2 * j) ∩ B = J₀ ∪ J₁ ∧
        (X (j - 1)).space ∩ T'' (2 * j) = J₀ ∧ (X j).space ∩ T'' (2 * j) = J₁ := by
      intro j hj
      rw [hother j (fun hjk => hks (hjk ▸ hj))]
      exact hann j (Finset.mem_insert_of_mem hj)
    have hE₀ : ∀ j, IsClosed (E₀ (2 * j)) := by
      intro j
      by_cases hj : j ∈ s
      · obtain ⟨B, J₀, J₁, hAj, -⟩ := hann₀ j hj
        obtain ⟨L, hLfin, -, -, hLs, -⟩ := hAj.exists_complex
        let _ : Finite L.faces := hLfin.to_subtype
        exact hLs ▸ (isPolyhedron_space L).isClosed
      · rw [houtside₀ j hj]
        exact (htw.boundary_isPolyhedron _).isClosed
    have hE₀T : ∀ j, E₀ (2 * j) ⊆ T'' (2 * j) := by
      intro j
      by_cases hj : j ∈ s
      · obtain ⟨B, J₀, J₁, -, -, hcov, -⟩ := hann₀ j hj
        exact subset_union_left.trans hcov.subset
      · rw [houtside₀ j hj]
    have hM₀ := ih E₀ houtside₀ hann₀
    have hM := hX.isSeparatorIn_after_replace_even_annulus htw hI havoid E₀ hE₀ hE₀T hM₀
      k (Function.update_self _ _ _) hA hB hcover hmeet hleft hright
    have hrestore : Function.update E₀ (2 * k) (E (2 * k)) = E := by
      funext j
      by_cases hj : j = 2 * k
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hj, E₀]
    exact hrestore ▸ hM

end DifferentialGeometry.Topology.PiecewiseLinear
