import DifferentialGeometry.Topology.SphereSeparation.SourceHeightCylinder
import DifferentialGeometry.Topology.Handle.SphereDiskSides

open Set Metric Manifold TopologicalSpace
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_innermost_source_height_cylinder_with_disk_sides {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {a : ℝ} (hne : ∃ x, e x 2 = a)
    (hr : ∀ x, e x 2 = a → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y => e y 2) x ≠ 0)
    {W : Set ℝ} (hW : IsOpen W) (haW : a ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ Icc (a - ε) (a + ε) ⊆ W ∧
      let T : Opens ℝ := ⟨Ioo (-ε) ε, isOpen_Ioo⟩
      ∃ R : ℝ, 1 < R ∧ ∃ (η : AddCircle (1 : ℝ) → SphereTwo)
        (Ψ : (Schoenflies.Plane × ℝ) ≃ₘ[ℝ] EuclideanThree)
        (q : AddCircle (1 : ℝ) → Schoenflies.Plane) (V : Opens SphereTwo)
        (C : (AddCircle (1 : ℝ) × T) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), 𝓡 2⟯ V),
        IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 2) ∞ η ∧
        IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ q ∧
        range q = sphere (0 : Schoenflies.Plane) 1 ∧
        (∀ p, Ψ p 2 = a + p.2) ∧
        Ψ ⁻¹' range e ∩ (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) =
          sphere (0 : Schoenflies.Plane) 1 ×ˢ Icc (-ε) ε ∧
        (V : Set SphereTwo) = e ⁻¹' (Ψ '' (sphere (0 : Schoenflies.Plane) 1 ×ˢ (T : Set ℝ))) ∧
        (∀ p, e (C p) = Ψ (q p.1, p.2.val)) ∧
        (∀ p, e (C p) 2 = a + p.2.val) ∧
        (∀ θ (t : T), t.val = 0 → (C (θ, t) : SphereTwo) = η θ) ∧
        ∃ b₀ b₁ : ClosedCell 2 → SphereTwo,
          IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₀ ∧
          IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b₁ ∧
          range (b₀ ∘ cellBoundaryInclusion 2) = range η ∧
          range (b₁ ∘ cellBoundaryInclusion 2) = range η ∧
          range b₀ ∪ range b₁ = univ ∧ range b₀ ∩ range b₁ = range η ∧
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            (∀ p, (C p : SphereTwo) ∈ interior (range b₀) ↔ σ * p.2.val < 0) ∧
            (∀ p, (C p : SphereTwo) ∈ interior (range b₁) ↔ 0 < σ * p.2.val) ∧
            (∀ p, (C p : SphereTwo) ∈ range b₀ ↔ σ * p.2.val ≤ 0) ∧
            (∀ p, (C p : SphereTwo) ∈ range b₁ ↔ 0 ≤ σ * p.2.val) := by
  obtain ⟨ε, hε, hεW, R, hR, η, Ψ, q, V, C, hη, hq, hqrange,
    hheight, hsphere, hV, hC, hCheight, hCzero⟩ :=
    exists_innermost_source_height_cylinder he hne hr hW haW
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, q, V, C, hη, hq, hqrange,
    hheight, hsphere, hV, hC, hCheight, hCzero, ?_⟩
  exact Handle.exists_two_smooth_disks_sphere_of_circle_with_cylinder_sides
    hη hε V C.toHomeomorph hCzero

end DifferentialGeometry.Topology.SphereSeparation
