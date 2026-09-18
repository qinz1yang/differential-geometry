/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCoordinates

/-! The five-triangle square model for the Moebius band. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

def mobiusSquareVertex : Fin 7 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (0, 1 / 4), (1, 1 / 2), (0, 3 / 4), (1, 1), (0, 1)]

def mobiusSquareTriangleVertex (i : Fin 5) (j : Fin 3) : ℝ × ℝ :=
  mobiusSquareVertex ⟨i.val + j.val, by omega⟩

def mobiusSquareTriangle (i : Fin 5) : Set (ℝ × ℝ) :=
  convexHull ℝ (range (mobiusSquareTriangleVertex i))

theorem mobiusSquareTriangleVertex_affineIndependent (i : Fin 5) :
    AffineIndependent ℝ (mobiusSquareTriangleVertex i) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hsum j
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hsum
  have hx := congrArg Prod.fst hsum
  have hy := congrArg Prod.snd hsum
  fin_cases i <;>
    norm_num [mobiusSquareTriangleVertex, mobiusSquareVertex, Fin.sum_univ_succ] at hx hy hw <;>
    fin_cases j <;> dsimp <;> linarith

private def squareTriangleCoord (i : Fin 5) (x : ℝ × ℝ) : ℝ × ℝ :=
  ![(4 * x.2, x.1), ((x.1 + 4 * x.2 - 1) / 2, 1 - x.1),
    ((4 * x.2 - x.1 - 1) / 2, x.1), ((x.1 + 4 * x.2 - 3) / 2, 1 - x.1),
    (4 * x.2 - x.1 - 3, x.1)] i

private theorem squareTriangleCoord_triangleAffineMap (i : Fin 5) (z : ℝ × ℝ) :
    squareTriangleCoord i (triangleAffineMap (mobiusSquareTriangleVertex i) z) = z := by
  fin_cases i <;> ext <;>
    simp [squareTriangleCoord, triangleAffineMap_apply, mobiusSquareTriangleVertex,
      mobiusSquareVertex] <;> ring

private theorem triangleAffineMap_squareTriangleCoord (i : Fin 5) (x : ℝ × ℝ) :
    triangleAffineMap (mobiusSquareTriangleVertex i) (squareTriangleCoord i x) = x := by
  fin_cases i <;> ext <;>
    simp [squareTriangleCoord, triangleAffineMap_apply, mobiusSquareTriangleVertex,
      mobiusSquareVertex] <;> ring

private theorem mem_mobiusSquareTriangle_iff (i : Fin 5) (x : ℝ × ℝ) :
    x ∈ mobiusSquareTriangle i ↔
      0 ≤ (squareTriangleCoord i x).1 ∧ 0 ≤ (squareTriangleCoord i x).2 ∧
        (squareTriangleCoord i x).1 + (squareTriangleCoord i x).2 ≤ 1 := by
  rw [mobiusSquareTriangle, ← triangleAffineMap_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [squareTriangleCoord_triangleAffineMap, mem_ofPred_eq] using hz
  · intro hx
    exact ⟨squareTriangleCoord i x, hx, triangleAffineMap_squareTriangleCoord i x⟩

theorem mem_mobiusSquareTriangle_zero_iff (x : ℝ × ℝ) :
    x ∈ mobiusSquareTriangle 0 ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + 4 * x.2 ≤ 1 := by
  rw [mem_mobiusSquareTriangle_iff]
  dsimp [squareTriangleCoord]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mem_mobiusSquareTriangle_one_iff (x : ℝ × ℝ) :
    x ∈ mobiusSquareTriangle 1 ↔ x.1 ≤ 1 ∧ 1 ≤ x.1 + 4 * x.2 ∧ 4 * x.2 ≤ x.1 + 1 := by
  rw [mem_mobiusSquareTriangle_iff]
  dsimp [squareTriangleCoord]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mem_mobiusSquareTriangle_two_iff (x : ℝ × ℝ) :
    x ∈ mobiusSquareTriangle 2 ↔ 0 ≤ x.1 ∧ x.1 + 1 ≤ 4 * x.2 ∧ x.1 + 4 * x.2 ≤ 3 := by
  rw [mem_mobiusSquareTriangle_iff]
  dsimp [squareTriangleCoord]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mem_mobiusSquareTriangle_three_iff (x : ℝ × ℝ) :
    x ∈ mobiusSquareTriangle 3 ↔ x.1 ≤ 1 ∧ 3 ≤ x.1 + 4 * x.2 ∧ 4 * x.2 ≤ x.1 + 3 := by
  rw [mem_mobiusSquareTriangle_iff]
  dsimp [squareTriangleCoord]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mem_mobiusSquareTriangle_four_iff (x : ℝ × ℝ) :
    x ∈ mobiusSquareTriangle 4 ↔ 0 ≤ x.1 ∧ x.2 ≤ 1 ∧ x.1 + 3 ≤ 4 * x.2 := by
  rw [mem_mobiusSquareTriangle_iff]
  dsimp [squareTriangleCoord]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem mobiusSquareTriangle_subset_square (i : Fin 5) :
    mobiusSquareTriangle i ⊆ Icc 0 1 ×ˢ Icc 0 1 := by
  intro x hx
  fin_cases i
  · obtain ⟨h₁, h₂, h₃⟩ := (mem_mobiusSquareTriangle_zero_iff x).mp hx
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · obtain ⟨h₁, h₂, h₃⟩ := (mem_mobiusSquareTriangle_one_iff x).mp hx
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · obtain ⟨h₁, h₂, h₃⟩ := (mem_mobiusSquareTriangle_two_iff x).mp hx
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · obtain ⟨h₁, h₂, h₃⟩ := (mem_mobiusSquareTriangle_three_iff x).mp hx
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · obtain ⟨h₁, h₂, h₃⟩ := (mem_mobiusSquareTriangle_four_iff x).mp hx
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem iUnion_mobiusSquareTriangle :
    (⋃ i, mobiusSquareTriangle i) = Icc 0 1 ×ˢ Icc 0 1 := by
  apply Subset.antisymm
  · exact iUnion_subset mobiusSquareTriangle_subset_square
  · rintro x ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩
    by_cases h₀ : x.1 + 4 * x.2 ≤ 1
    · exact mem_iUnion.mpr ⟨0, (mem_mobiusSquareTriangle_zero_iff x).mpr ⟨hx₀, hy₀, h₀⟩⟩
    by_cases h₁ : 4 * x.2 ≤ x.1 + 1
    · exact mem_iUnion.mpr ⟨1, (mem_mobiusSquareTriangle_one_iff x).mpr
        ⟨hx₁, le_of_not_ge h₀, h₁⟩⟩
    by_cases h₂ : x.1 + 4 * x.2 ≤ 3
    · exact mem_iUnion.mpr ⟨2, (mem_mobiusSquareTriangle_two_iff x).mpr
        ⟨hx₀, le_of_not_ge h₁, h₂⟩⟩
    by_cases h₃ : 4 * x.2 ≤ x.1 + 3
    · exact mem_iUnion.mpr ⟨3, (mem_mobiusSquareTriangle_three_iff x).mpr
        ⟨hx₁, le_of_not_ge h₂, h₃⟩⟩
    exact mem_iUnion.mpr ⟨4, (mem_mobiusSquareTriangle_four_iff x).mpr
      ⟨hx₀, hy₁, le_of_not_ge h₃⟩⟩

end

end DifferentialGeometry.Topology.PiecewiseLinear
