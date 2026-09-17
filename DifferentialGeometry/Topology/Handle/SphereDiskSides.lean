import DifferentialGeometry.Topology.Handle.SphereDisk
import DifferentialGeometry.Topology.SphereSeparation.CylinderSides

open Set Metric TopologicalSpace
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hη : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η)
    {ε : ℝ} (hε : 0 < ε) (V : Opens SphereTwo)
    (C : (AddCircle (1 : ℝ) × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : Opens ℝ)) ≃ₜ V)
    (hCzero : ∀ θ t, t.val = 0 → (C (θ, t) : SphereTwo) = η θ) :
    ∃ b₀ b₁ : ClosedCell 2 → SphereTwo,
      Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₀ ∧
      Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₁ ∧
      range (b₀ ∘ cellBoundaryInclusion 2) = range η ∧
      range (b₁ ∘ cellBoundaryInclusion 2) = range η ∧
      range b₀ ∪ range b₁ = univ ∧ range b₀ ∩ range b₁ = range η ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        (∀ p, (C p : SphereTwo) ∈ interior (range b₀) ↔ σ * p.2.val < 0) ∧
        (∀ p, (C p : SphereTwo) ∈ interior (range b₁) ↔ 0 < σ * p.2.val) ∧
        (∀ p, (C p : SphereTwo) ∈ range b₀ ↔ σ * p.2.val ≤ 0) ∧
        (∀ p, (C p : SphereTwo) ∈ range b₁ ↔ 0 ≤ σ * p.2.val) := by
  obtain ⟨b₀, b₁, hb₀, hb₁, hboundary₀, hboundary₁, hcover, hinter⟩ :=
    exists_two_smooth_disks_sphere_of_circle hη
  have hregular₀ := closure_interior_range_closedCell_sphere 1 hb₀
  have hregular₁ := closure_interior_range_closedCell_sphere 1 hb₁
  have hfrontier₀ := (frontier_range_closedCell_sphere 1 hb₀).trans hboundary₀
  have hfrontier₁ := (frontier_range_closedCell_sphere 1 hb₁).trans hboundary₁
  let _ : Nonempty (ClosedCell 2) := ⟨⟨0, by simp⟩⟩
  let d := SphereSeparation.TwoSidedSeparation.ofClosedCover hregular₀ hregular₁
    (range_nonempty b₀) (range_nonempty b₁) hcover hinter hfrontier₀ hfrontier₁
  let T : Opens ℝ := ⟨Ioo (-ε) ε, isOpen_Ioo⟩
  let z : T := ⟨0, by constructor <;> linarith⟩
  have hzero : ∀ p, (C p : SphereTwo) ∈ range η ↔ p.2.val = 0 := by
    intro p
    constructor
    · rintro ⟨θ, hθ⟩
      have hpair : C p = C (θ, z) := Subtype.ext (hθ.symm.trans (hCzero θ z rfl).symm)
      exact congrArg (fun q => q.2.val) (C.injective hpair)
    · intro hp
      exact ⟨p.1, (hCzero p.1 p.2 hp).symm⟩
  obtain ⟨σ, hσ, h₀, h₁, hc₀, hc₁⟩ := d.sides_of_cylinder hε V C hzero
  refine ⟨b₀, b₁, hb₀, hb₁, hboundary₀, hboundary₁, hcover, hinter, σ, hσ, h₀, h₁, ?_, ?_⟩
  · simpa only [d, SphereSeparation.TwoSidedSeparation.ofClosedCover, hregular₀] using hc₀
  · simpa only [d, SphereSeparation.TwoSidedSeparation.ofClosedCover, hregular₁] using hc₁

end DifferentialGeometry.Topology.Handle
