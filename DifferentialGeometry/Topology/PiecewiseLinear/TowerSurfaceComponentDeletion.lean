/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def IsTypeOneDeletion (I H K C R X X' F : Set E3) : Prop :=
  X = C ∪ R ∧ Disjoint C R ∧ IsClosed (((↑) : I → E3) ⁻¹' C) ∧
    IsClosed (((↑) : I → E3) ⁻¹' R) ∧
    ¬ Separates (((↑) : I → E3) ⁻¹' C) (((↑) : I → E3) ⁻¹' H)
      (((↑) : I → E3) ⁻¹' K) ∧
    X' = R ∧ IsSeparatorIn I X' H K ∧ X' ∩ F = X ∩ F

theorem towerSurface_update_eq_sdiff (T L : ℤ → Set E3) (P' : E3) (i : ℤ) (C : Set E3)
    (hCT : ∀ j, Disjoint C (T (2 * j)))
    (hCL : ∀ j, j ≠ i → Disjoint C (L j)) (hP : P' ∉ C) :
    towerSurface T (Function.update L i (L i \ C)) P' = towerSurface T L P' \ C := by
  classical
  ext x
  constructor
  · rintro (hx | hxP)
    · obtain ⟨j, hxT | hxL⟩ := mem_iUnion.mp hx
      · exact ⟨Or.inl (mem_iUnion.mpr ⟨j, Or.inl hxT⟩), disjoint_left.mp (hCT j).symm hxT⟩
      · by_cases hji : j = i
        · subst j
          rw [Function.update_self] at hxL
          exact ⟨Or.inl (mem_iUnion.mpr ⟨i, Or.inr hxL.1⟩), hxL.2⟩
        · rw [Function.update_of_ne hji] at hxL
          exact ⟨Or.inl (mem_iUnion.mpr ⟨j, Or.inr hxL⟩),
            disjoint_left.mp (hCL j hji).symm hxL⟩
    · exact ⟨Or.inr hxP, fun hxC => hP (hxP ▸ hxC)⟩
  · rintro ⟨hx | hxP, hxC⟩
    · obtain ⟨j, hxT | hxL⟩ := mem_iUnion.mp hx
      · exact Or.inl (mem_iUnion.mpr ⟨j, Or.inl hxT⟩)
      · apply Or.inl
        refine mem_iUnion.mpr ⟨j, Or.inr ?_⟩
        by_cases hji : j = i
        · subst j
          rw [Function.update_self]
          exact ⟨hxL, hxC⟩
        · rwa [Function.update_of_ne hji]
    · exact Or.inr hxP

end DifferentialGeometry.Topology.PiecewiseLinear
