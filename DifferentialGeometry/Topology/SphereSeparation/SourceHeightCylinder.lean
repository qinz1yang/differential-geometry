import DifferentialGeometry.Topology.SphereSeparation.HeightCylinder
import DifferentialGeometry.Topology.Embedding.Cylinder

open Set Metric Manifold TopologicalSpace
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_innermost_source_height_cylinder {e : SphereTwo → EuclideanThree}
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
        ∀ θ (t : T), t.val = 0 → (C (θ, t) : SphereTwo) = η θ := by
  obtain ⟨ε, hε, hεW, R, hR, η, Ψ, hη, hheight, hboundary, hsphere⟩ :=
    exists_innermost_height_cylinder_chart he hne hr hW haW
  let T : Opens ℝ := ⟨Ioo (-ε) ε, isOpen_Ioo⟩
  have hwall : ∀ x ∈ sphere (0 : Schoenflies.Plane) 1, ∀ t ∈ T, Ψ (x, t) ∈ range e := by
    intro x hx t ht
    have hp : (x, t) ∈ Ψ ⁻¹' range e ∩
        (closedBall (0 : Schoenflies.Plane) R ×ˢ Icc (-ε) ε) :=
      hsphere.symm.subset ⟨hx, Ioo_subset_Icc_self ht⟩
    exact hp.1
  obtain ⟨q, hq, hqrange, V, C, hV, hC, hCzero⟩ :=
    he.exists_cylinder_diffeomorph hη Ψ T hboundary hwall
  refine ⟨ε, hε, hεW, R, hR, η, Ψ, q, V, C, hη, hq, hqrange,
    hheight, hsphere, hV, hC, ?_, hCzero⟩
  intro p
  rw [hC, hheight]

end DifferentialGeometry.Topology.SphereSeparation
