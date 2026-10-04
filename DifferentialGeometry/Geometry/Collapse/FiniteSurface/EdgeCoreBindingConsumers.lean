import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreBinding

/-!
# Consumer of LFR24

`exists_edge_core_smooth_disk_four`: with `ε = μ = 1/200`, an endpoint model of error
`δ ≤ 1/(200² · 24000000)` gives a function `h`, smooth near `B̄(z₀, 9)`, whose sublevel `D_4` is a smooth
closed disk between `B̄(z₀, 4 - 1/200)` and `B(z₀, 4 + 1/200)` with regular boundary level.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Function Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

/-- **Consumer (LFR24).** For small endpoint error the core sublevel `D_4` is a smooth closed disk
in the annulus `4 - 1/200 ≤ r < 4 + 1/200`. -/
theorem exists_edge_core_smooth_disk_four (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    ∃ δ₀ > 0, ∀ (z₀ : Z) (q : Z → ℝ) (δ : ℝ), 0 < δ → δ ≤ δ₀ → q z₀ = 0 →
      (∀ y ∈ closedBall z₀ 10, 0 ≤ q y) →
      (∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ) →
      (∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) →
      ∃ h : Z → ℝ, closedBall z₀ (4 - 1 / 200) ⊆ {x | dist x z₀ < 9 ∧ h x ≤ 4} ∧
        {x | dist x z₀ < 9 ∧ h x ≤ 4} ⊆ ball z₀ (4 + 1 / 200) ∧
        ∃ b : ClosedCell 2 → Z, Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
          range b = {x | dist x z₀ < 9 ∧ h x ≤ 4} := by
  obtain ⟨δ₀, hδ₀, hcore⟩ := finiteSurface_edge_model_core o k hr hnorm hK (ε := 1 / 200)
    (by norm_num) (by norm_num)
  refine ⟨δ₀, hδ₀, fun z₀ q δ hδ hδδ hq0 hqnn hdist hdense => ?_⟩
  obtain ⟨h, -, -, -, -, hdisk, -⟩ := hcore z₀ q δ hδ hδδ hq0 hqnn hdist hdense (1 / 200)
    (by norm_num) (by norm_num)
  obtain ⟨-, hsub, hsup, b, hb, hbr, -⟩ := hdisk 4 ⟨by norm_num, by norm_num⟩
  exact ⟨h, hsub, hsup, b, hb, hbr⟩

end DifferentialGeometry.Geometry.Collapse
