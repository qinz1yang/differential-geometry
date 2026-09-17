import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Tauto

open Set

namespace DifferentialGeometry.Topology

theorem frontier_inter_of_isClosed {X : Type*} [TopologicalSpace X] {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q) :
    frontier (P ∩ Q) = (frontier P ∩ Q) ∪ (P ∩ frontier Q) := by
  ext x
  simp only [frontier, hP.closure_eq, hQ.closure_eq, (hP.inter hQ).closure_eq,
    interior_inter, mem_sdiff, mem_inter_iff, mem_union]
  tauto

theorem frontier_inter_preimage_Icc_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsClosed P) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {a b : ℝ} (hab : a ≤ b) :
    frontier (P ∩ ℓ ⁻¹' Icc a b) = (frontier P ∩ ℓ ⁻¹' Icc a b) ∪ (P ∩ ℓ ⁻¹' {a, b}) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) h
  have hopen : IsOpenMap ℓ := ℓ.toLinearMap.isOpenMap_of_finiteDimensional (LinearMap.surjective hlinear)
  rw [frontier_inter_of_isClosed hP (isClosed_Icc.preimage ℓ.continuous),
    ← hopen.preimage_frontier_eq_frontier_preimage ℓ.continuous, frontier_Icc hab]

end DifferentialGeometry.Topology
