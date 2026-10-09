/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_affineEquiv_prod_coord_zero {E : Type*}
    [AddCommGroup E] [Module ℝ E] (b : AffineBasis (Fin 4) ℝ E) :
    ∃ g : E ≃ᵃ[ℝ] (ℝ × ℝ × ℝ), ∀ x, (g x).2.2 = b.coord 0 x := by
  let f : E →ᵃ[ℝ] (ℝ × ℝ × ℝ) := (b.coord 1).prod ((b.coord 2).prod (b.coord 0))
  have hinj : Function.Injective f := by
    intro x y hxy
    have h0 : b.coord 0 x = b.coord 0 y := congrArg (fun p => p.2.2) hxy
    have h1 : b.coord 1 x = b.coord 1 y := congrArg Prod.fst hxy
    have h2 : b.coord 2 x = b.coord 2 y := congrArg (fun p => p.2.1) hxy
    have h3 : b.coord 3 x = b.coord 3 y := by
      have hx := b.sum_coord_apply_eq_one x
      have hy := b.sum_coord_apply_eq_one y
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hx hy
      change b.coord 0 x + (b.coord 1 x + (b.coord 2 x + b.coord 3 x)) = 1 at hx
      change b.coord 0 y + (b.coord 1 y + (b.coord 2 y + b.coord 3 y)) = 1 at hy
      linarith
    apply b.ext_elem
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hsurj : Function.Surjective f := by
    intro p
    let w : Fin 4 → ℝ := ![p.2.2, p.1, p.2.1, 1 - p.2.2 - p.1 - p.2.1]
    have hw : Finset.univ.sum w = 1 := by
      simp [Fin.sum_univ_succ, w]
    refine ⟨Finset.univ.affineCombination ℝ b w, ?_⟩
    apply Prod.ext
    · exact b.coord_apply_combination_of_mem (Finset.mem_univ 1) hw
    · apply Prod.ext
      · exact b.coord_apply_combination_of_mem (Finset.mem_univ 2) hw
      · exact b.coord_apply_combination_of_mem (Finset.mem_univ 0) hw
  exact ⟨AffineEquiv.ofBijective ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem exists_affineEquiv_prod_coord_of_affineBasis {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (b : AffineBasis ι ℝ E) (hcard : Fintype.card ι = 4)
    (i : ι) : ∃ g : E ≃ᵃ[ℝ] (ℝ × ℝ × ℝ), ∀ x, (g x).2.2 = b.coord i x := by
  classical
  let e₀ : ι ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let e : ι ≃ Fin 4 := e₀.trans (Equiv.swap (e₀ i) 0)
  have hi : e i = 0 := by simp [e]
  obtain ⟨g, hg⟩ := exists_affineEquiv_prod_coord_zero (b.reindex e)
  refine ⟨g, fun x => ?_⟩
  rw [hg, AffineBasis.coord_reindex, ← hi, e.symm_apply_apply]

end DifferentialGeometry.Topology.PiecewiseLinear
