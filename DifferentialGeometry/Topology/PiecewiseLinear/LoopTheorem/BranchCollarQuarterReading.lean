/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarSides
import DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeLabels
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchTubeCharts

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem mem_source_quarter_iff_crossHalfPlane (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {A : Bool → Set (EuclideanSpace ℝ (Fin 2))} (hAC : ∀ b, A b ⊆ C)
    {U : Set M} {e : M → ℝ × ℝ × ℝ}
    (hsheet : ∀ b y, y ∈ U → (y ∈ D '' A b ↔ if b then (e y).2.1 = 0 else (e y).2.2 = 0))
    (hbranch : ∀ y ∈ U, y ∈ hD.singularSet.branchCarrier c ↔ (e y).2 = 0)
    (hpos : ∀ b x, x ∈ A b →
      (0 < (if b then (e (D x)).2.2 else (e (D x)).2.1) ↔
        ∃ s ∈ Ioc (0 : ℝ) 1, ∃ w ∈ J, x = ρ (w, s)))
    (i : Fin 4) {y : M} (hy : y ∈ U) :
    y ∈ D '' (A (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2) ↔
      crossNormalFormEquiv (e y) ∈ crossHalfPlane i := by
  let b := (fourSpokeLabel i).1
  let positive := (fourSpokeLabel i).2
  have hside : ∀ x ∈ A b, D x ∈ U →
      (x ∈ collarHalf J ρ positive ↔
        if positive then 0 ≤ (if b then (e (D x)).2.2 else (e (D x)).2.1)
        else (if b then (e (D x)).2.2 else (e (D x)).2.1) ≤ 0) := by
    intro x hx hxU
    apply hD.mem_collarHalf_iff_coordinate hρ (hAC b hx) _ (hpos b x hx) positive
    rw [hbranch _ hxU]
    have hother := (hsheet b (D x) hxU).mp ⟨x, hx, rfl⟩
    cases hb : b
    · simp only [hb, Bool.false_eq_true, ite_false] at hother ⊢
      constructor
      · intro hz
        exact Prod.ext hz hother
      · intro hz
        exact congrArg Prod.fst hz
    · simp only [hb, ite_true] at hother ⊢
      constructor
      · intro hz
        exact Prod.ext hother hz
      · intro hz
        exact congrArg Prod.snd hz
  rw [mem_crossHalfPlane_iff_label]
  change y ∈ D '' (A b ∩ collarHalf J ρ positive) ↔
    (if b then (e y).2.1 = 0 else (e y).2.2 = 0) ∧
    (if positive then 0 ≤ (if b then (e y).2.2 else (e y).2.1)
      else (if b then (e y).2.2 else (e y).2.1) ≤ 0)
  constructor
  · rintro ⟨x, ⟨hxA, hxH⟩, rfl⟩
    exact ⟨(hsheet b _ hy).mp ⟨x, hxA, rfl⟩, (hside x hxA hy).mp hxH⟩
  · rintro ⟨hs, hsgn⟩
    obtain ⟨x, hxA, rfl⟩ := (hsheet b _ hy).mpr hs
    exact ⟨x, ⟨hxA, (hside x hxA hy).mpr hsgn⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
