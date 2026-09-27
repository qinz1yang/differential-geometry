/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeComponentDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningWindowReduction
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusReversal

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCanonicalAnnularWindow.bridge_component_of_not_returning [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {S' S'' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3} {rows : Finset ℤ}
    (hX : IsCanonicalAnnularWindow X S' S'' T I P' a b rows)
    (i : ℤ) (hi : i ∈ rows) (c : ConnectedComponents (X i).space)
    (hno : ¬ IsCanonicalReturningComponent X T i c) :
    IsCanonicalBridgeComponent X T i c := by
  obtain ⟨J₀, J₁, hC, hdis, h₀, h₁, hess₀, hess₁⟩ := hX.components i hi c
  rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
  · exact (hno ⟨i, J₀, J₁, Or.inl rfl, hC, hdis, h₀, h₁, hess₀, hess₁⟩).elim
  · exact ⟨J₀, J₁, hC, h₀, h₁, hess₀, hess₁⟩
  · exact ⟨J₁, J₀, hC.symm, h₁, h₀, hess₁, hess₀⟩
  · exact (hno ⟨i + 1, J₀, J₁, Or.inr rfl, hC, hdis, h₀, h₁, hess₀, hess₁⟩).elim

theorem IsCanonicalReturningWindowReduction.bridge_components [DecidableEq E3]
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {S' S'' T : ℤ → Set E3}
    {I F : Set E3} {P' a b : E3} {rows : Finset ℤ}
    (h : IsCanonicalReturningWindowReduction X Y S' S'' T I P' a b rows F)
    (i : ℤ) (hi : i ∈ rows) (c : ConnectedComponents (Y i).space) :
    IsCanonicalBridgeComponent Y T i c :=
  h.target.bridge_component_of_not_returning i hi c (h.returningFree i hi c)

end DifferentialGeometry.Topology.PiecewiseLinear
