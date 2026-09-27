/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexRadialExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.PolytopeBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Product

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_prism_fixed_axis
    {P : Set E} (hP : IsHPolytope P) {p : E} (hp : p ∈ interior P)
    {f : E × ℝ → E × ℝ}
    (hf : IsPLHomeomorphOn f (frontier (P ×ˢ Icc (0 : ℝ) 1))
      (frontier (P ×ˢ Icc (0 : ℝ) 1)))
    (hf0 : f (p, 0) = (p, 0)) (hf1 : f (p, 1) = (p, 1)) :
    ∃ g : E × ℝ → E × ℝ,
      IsPLHomeomorphOn g (P ×ˢ Icc (0 : ℝ) 1) (P ×ˢ Icc (0 : ℝ) 1) ∧
      EqOn g f (frontier (P ×ˢ Icc (0 : ℝ) 1)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, g (p, t) = (p, t) := by
  have hQ : IsHPolytope (P ×ˢ Icc (0 : ℝ) 1) := hP.prod isHPolytope_Icc
  have hq : (p, (1 / 2 : ℝ)) ∈ interior (P ×ˢ Icc (0 : ℝ) 1) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hp, by norm_num⟩
  obtain ⟨g, hg, hgf, -, hgr⟩ := exists_isPLHomeomorphOn_of_convex_frontier
    hQ.convex hQ.convex hQ.isCompact hQ.isCompact
    hQ.isPolyhedron_frontier hQ.isPolyhedron_frontier hq hq hf
  have hend : ∀ a ∈ ({0, 1} : Set ℝ), (p, a) ∈ frontier (P ×ˢ Icc (0 : ℝ) 1) := by
    intro a ha
    rw [frontier_prod_eq, hP.isClosed.closure_eq, frontier_Icc zero_le_one]
    exact Or.inl ⟨interior_subset hp, ha⟩
  refine ⟨g, hg, hgf, fun t ht => ?_⟩
  rcases le_total t (1 / 2) with htle | htle
  · have hs : 1 - 2 * t ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ht.1]
    have h := hgr (p, 0) (hend 0 (Or.inl rfl)) (1 - 2 * t) hs
    rw [hf0] at h
    have heq : (p, (1 / 2 : ℝ)) + (1 - 2 * t) •
        ((p, (0 : ℝ)) - (p, (1 / 2 : ℝ))) = (p, t) := by
      apply Prod.ext
      · simp
      · dsimp
        ring
    simpa only [heq] using h
  · have hs : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ht.2]
    have h := hgr (p, 1) (hend 1 (Or.inr rfl)) (2 * t - 1) hs
    rw [hf1] at h
    have heq : (p, (1 / 2 : ℝ)) + (2 * t - 1) •
        ((p, (1 : ℝ)) - (p, (1 / 2 : ℝ))) = (p, t) := by
      apply Prod.ext
      · simp
      · dsimp
        ring
    simpa only [heq] using h

end DifferentialGeometry.Topology.PiecewiseLinear
