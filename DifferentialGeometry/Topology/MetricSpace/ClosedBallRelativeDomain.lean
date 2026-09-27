import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Constructions

section

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem isOpen_image_of_relatively_open_closedBall
    {R : ℝ} {S : Set (Metric.closedBall (0 : V) R)} (hS : IsOpen S)
    (hsub : ∀ x ∈ S, (x : V) ∈ Metric.ball (0 : V) R) :
    IsOpen (Subtype.val '' S : Set V) := by
  obtain ⟨U, hU, hUeq⟩ := hS.image_val
  have heq : (Subtype.val '' S : Set V) = U ∩ Metric.ball (0 : V) R := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨(hUeq ▸ mem_image_of_mem Subtype.val hy).1, hsub y hy⟩
    · intro x hx
      rw [hUeq]
      exact ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩
  rw [heq]
  exact hU.inter Metric.isOpen_ball

theorem mem_frontier_relative_of_mem_frontier_image_closedBall
    {R : ℝ} {S : Set (Metric.closedBall (0 : V) R)} (hS : IsOpen S)
    (hsub : ∀ x ∈ S, (x : V) ∈ Metric.ball (0 : V) R)
    {x : V} (hx : x ∈ frontier (Subtype.val '' S : Set V)) :
    ∃ hxR : x ∈ Metric.closedBall (0 : V) R,
      (⟨x, hxR⟩ : Metric.closedBall (0 : V) R) ∈ frontier S := by
  have hcl : closure (Subtype.val '' S : Set V) ⊆ Metric.closedBall (0 : V) R :=
    closure_minimal (by rintro x ⟨y, _, rfl⟩; exact y.property) Metric.isClosed_closedBall
  have hxR := hcl hx.1
  refine ⟨hxR, ?_, ?_⟩
  · exact closure_subtype.mpr hx.1
  · rw [hS.interior_eq]
    intro hxS
    apply hx.2
    rw [(isOpen_image_of_relatively_open_closedBall hS hsub).interior_eq]
    exact mem_image_of_mem Subtype.val hxS

end DifferentialGeometry.Analysis

end

end
