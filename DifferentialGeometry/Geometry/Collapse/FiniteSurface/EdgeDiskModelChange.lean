import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreBinding
import DifferentialGeometry.Topology.Manifold.ModelChange.ContinuousLinearEquiv

/-!
The actual LFR24 disk embedding uses the same underlying points in the coordinate-function model.
Both smooth embedding structures and its sublevel and boundary images are retained.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Function
open DifferentialGeometry.Manifold DifferentialGeometry.Topology
open DifferentialGeometry.Manifold.LinearModelChange
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "L" => EuclideanSpace.equiv (Fin 2) ℝ
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace
open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold
variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]
variable (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
  (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
    (TangentSpace (𝓡 2) : Z → Type _)) (hr : 3 ≤ r)
  (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
  (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
  {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 100)
include o hr hnorm hK hε hε1 in
theorem exists_edge_model_disk_piModel :
  ∃ δ₀ > 0, ∀ (z₀ : Z) (q : Z → ℝ) (δ : ℝ), 0 < δ → δ ≤ δ₀ → q z₀ = 0 →
  (∀ y ∈ closedBall z₀ 10, 0 ≤ q y) →
  (∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ) →
  (∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) →
  ∀ μ : ℝ, 0 < μ → μ < 1 / 100 →
  ∃ h : Z → ℝ, ∀ s ∈ Icc (3 : ℝ) 6,
    IsCompact {x : Z | dist x z₀ < 9 ∧ h x ≤ s} ∧
    closedBall z₀ (s - μ) ⊆ {x | dist x z₀ < 9 ∧ h x ≤ s} ∧
    {x | dist x z₀ < 9 ∧ h x ≤ s} ⊆ ball z₀ (s + μ) ∧
    ∃ b : ClosedCell 2 → LinearModelChange Z L,
      IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, Fin 2 → ℝ) ∞ b ∧
      IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (fun p => LinearModelChange.toBase L (b p)) ∧
      range b = {x | dist (LinearModelChange.toBase L x) z₀ < 9 ∧
        h (LinearModelChange.toBase L x) ≤ s} ∧
      range (b ∘ cellBoundaryInclusion 2) =
        {x | dist (LinearModelChange.toBase L x) z₀ < 9 ∧
          h (LinearModelChange.toBase L x) = s} := by
  obtain ⟨δ₀, hδ₀, hrow⟩ := finiteSurface_edge_model_core o k hr hnorm hK hε hε1
  refine ⟨δ₀, hδ₀, ?_⟩
  intro z₀ q δ hδ hδ0 hq0 hqnn hdist hdense μ hμ hμ1
  obtain ⟨h, _hsmooth, _hzero, _hsmall, _hgrad, hdisks, _hfield, _hregular, _henclosure⟩ :=
    hrow z₀ q δ hδ hδ0 hq0 hqnn hdist hdense μ hμ hμ1
  refine ⟨h, ?_⟩
  intro s hs
  obtain ⟨hcompact, hinner, houter, b, hb, hrange, hboundary⟩ := hdisks s hs
  refine ⟨hcompact, hinner, houter, fun p => LinearModelChange.ofBase L (b p), ?_, hb, ?_, ?_⟩
  · exact (isSmoothEmbedding_toLinearModelChange_iff (X := Z) (I₀ := 𝓡∂ 2) L).mpr hb
  · exact hrange
  · exact hboundary
end DifferentialGeometry.Geometry.Collapse
