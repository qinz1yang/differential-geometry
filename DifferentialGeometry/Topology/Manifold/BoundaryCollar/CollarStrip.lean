import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ClosedStripDiffeomorph

open Set Function Filter Manifold
open scoped Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar

theorem exists_smooth_boundary_collar_strip
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ c : BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε → M,
        Topology.IsClosedEmbedding c ∧
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ c ∧
        (∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        (∀ p (t : Icc (0 : ℝ) ε), 0 < (t : ℝ) → (𝓡∂ (n + 1)).IsInteriorPoint (c (p, t))) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
          IsOpen (c '' {q | (q.2 : ℝ) < δ}) ∧
          (𝓡∂ (n + 1)).boundary M ⊆ c '' {q | (q.2 : ℝ) < δ} := by
  obtain ⟨ε, hε, c, hc, hcs, hc0, hi, δ, hδ, hδε, Y, hKY, hY, _, _⟩ :=
    exists_closed_boundary_collar_diffeomorph hK
  refine ⟨ε, hε, c, hc, hcs, hc0, (fun p t ht => hi (p, t) ht),
    δ, hδ, hδε, ?_, ?_⟩
  · exact hY ▸ Y.isOpen
  · exact hY ▸ hKY

end Poincare.Manifold.BoundaryCollar
