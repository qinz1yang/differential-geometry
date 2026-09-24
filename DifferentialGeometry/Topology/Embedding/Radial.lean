import DifferentialGeometry.Topology.Diffeomorph.Radial
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Handle.Embedding

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

private theorem smooth_closedCell_filling_of_diffeomorph (n : ℕ)
    (F : EuclideanSpace ℝ (Fin (n + 1)) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ b : ClosedCell (n + 1) → EuclideanSpace ℝ (Fin (n + 1)),
      Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace (n + 1))
        (𝓡 (n + 1)) ∞ b ∧
      (∀ x, b x = F x.val) ∧
      Set.range b = F '' Metric.closedBall 0 1 ∧
      Set.range (b ∘ cellBoundaryInclusion (n + 1)) = F '' Metric.sphere 0 1 := by
  refine ⟨F ∘ Subtype.val,
    (Handle.closedCellInclusion_isSmoothEmbedding n).diffeomorph_comp F,
    fun _ => rfl, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, by simpa using x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, by simpa using hx⟩, rfl⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, by simpa using x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, by simpa using hx⟩, rfl⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_smooth_radial_ball_filling (n : ℕ)
    (R : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → ℝ)
    (hR : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R) (hpos : ∀ θ, 0 < R θ) :
    ∃ b : ClosedCell (n + 1) → EuclideanSpace ℝ (Fin (n + 1)),
      Manifold.IsSmoothEmbedding (modelWithCornersEuclideanHalfSpace (n + 1)) (𝓡 (n + 1)) ∞ b ∧
      b (closedCellCenter (n + 1)) = 0 ∧
      Set.range b =
        {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          ∃ s : ℝ, 0 < s ∧ s ≤ R θ ∧ z = s • (θ : EuclideanSpace ℝ (Fin (n + 1)))} ∧
      Set.range (b ∘ cellBoundaryInclusion (n + 1)) =
        Set.range (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =>
          R θ • (θ : EuclideanSpace ℝ (Fin (n + 1)))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  obtain ⟨F, hzero, _, _, hclosed, _, hsphere⟩ :=
    Diffeomorph.exists_diffeomorph_eq_smul_on_sphere (d := n) R hR hpos
  obtain ⟨b, hb, hbF, hball, hboundary⟩ := smooth_closedCell_filling_of_diffeomorph n F
  refine ⟨b, hb, ?_, hball.trans hclosed, hboundary.trans hsphere⟩
  rw [hbF]
  exact hzero

end DifferentialGeometry.Topology
