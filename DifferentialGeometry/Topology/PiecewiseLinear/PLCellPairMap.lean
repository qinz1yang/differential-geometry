/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_isPLHomeomorphInto_cells {d : ℕ}
    {P PB : Set M₁} {Q QB : Set M₂}
    (hP : IsPLCellOn d P PB) (hQ : IsPLCellOn d Q QB) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f P ∧
      f '' P = Q ∧ f '' PB = QB := by
  classical
  obtain ⟨A, r, u, hr, hu, rfl, rfl⟩ := hP
  obtain ⟨B, s, v, hs, hv, rfl, rfl⟩ := hQ
  let H := s ∘ Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)))
  have hH : IsPLHomeomorphOn H A B := hr.symm.trans hs
  obtain ⟨hf, hfim⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn hu hv hH
  refine ⟨v ∘ H ∘ Function.invFunOn u A, hf, hfim, ?_⟩
  have hbsub : stdSimplexBoundary d ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)) :=
    fun _ hx => hx.1
  have hAsub : r '' stdSimplexBoundary d ⊆ A := by
    rw [← hr.image_eq]
    exact image_mono hbsub
  have hrinv : Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) ''
      (r '' stdSimplexBoundary d) = stdSimplexBoundary d := by
    rw [← image_comp]
    have h : EqOn (Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1))) ∘ r)
        id (stdSimplexBoundary d) :=
      fun x hx => hr.bijOn.invOn_invFunOn.1 (hbsub hx)
    exact h.image_eq.trans (image_id _)
  have huinv : Function.invFunOn u A '' (u '' (r '' stdSimplexBoundary d)) =
      r '' stdSimplexBoundary d := by
    rw [← image_comp]
    have h : EqOn (Function.invFunOn u A ∘ u) id (r '' stdSimplexBoundary d) :=
      fun x hx => hu.injOn.leftInvOn_invFunOn (hAsub hx)
    exact h.image_eq.trans (image_id _)
  calc
    (v ∘ H ∘ Function.invFunOn u A) '' (u '' (r '' stdSimplexBoundary d))
        = v '' (H '' (Function.invFunOn u A '' (u '' (r '' stdSimplexBoundary d)))) := by
            rw [image_comp, image_comp]
    _ = v '' (H '' (r '' stdSimplexBoundary d)) := by rw [huinv]
    _ = v '' (s '' stdSimplexBoundary d) := by
      congr 1
      change (s ∘ Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)))) ''
        (r '' stdSimplexBoundary d) = _
      rw [image_comp, hrinv]

end DifferentialGeometry.Topology.PiecewiseLinear
