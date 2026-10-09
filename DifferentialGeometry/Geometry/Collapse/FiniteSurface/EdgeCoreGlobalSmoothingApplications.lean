import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreGlobalSmoothing
import DifferentialGeometry.Geometry.Collapse.EdgeModelFibreDisk

/-!
# Consumer: the exported LFR24 smoothing in LFR28's physical profile form

`finiteSurface_edge_model_core_global` composed with the I6 assembly
`edgeModelCylinder_fibre_closedCell`: for every `Δ > 0` the physical model smoothing `G = ΔF` has
GLOBAL value error `|G - Δr| < μΔ` (Codex X100's `hG` shape), the model height is
`H_N = Δψ(G/Δ) = Δh` (the SAME fixed profile as the source), and the model fibre
`{t = 0, H_N ≤ 4Δ}` of the cylinder `(-6Δ, 6Δ) × B(z₀, 9)` is homeomorphic to `ClosedCell 2`
(`finiteSurface_edge_model_global_profile`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Function Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology DifferentialGeometry.Manifold.RegularLevel

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

/-- **Concrete consumer.** LFR24 with its exported smoothing gives, at every physical scale `Δ`, a
model smoothing `G = ΔF` with global error `μΔ`, the profile identity `Δh = Δψ(G/Δ)`, and a model
fibre homeomorphic to the closed disk. -/
theorem finiteSurface_edge_model_global_profile (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 100) :
    ∃ δ₀ > 0, ∀ (z₀ : Z) (q : Z → ℝ) (δ : ℝ), 0 < δ → δ ≤ δ₀ → q z₀ = 0 →
      (∀ y ∈ closedBall z₀ 10, 0 ≤ q y) →
      (∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ) →
      (∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) →
      ∀ μ : ℝ, 0 < μ → μ < 1 / 100 →
      ∃ F : Z → ℝ, ∀ Δ : ℝ, 0 < Δ →
        (∀ x, |Δ * F x - Δ * dist x z₀| < μ * Δ) ∧
        (∀ x, Δ * edgeModelCore F x =
          Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (Δ * F x / Δ)) ∧
        Nonempty (ClosedCell 2 ≃ₜ {x : edgeModelCylinder z₀ Δ //
          (((x : ℝ × Z).1, Δ * edgeModelCore F (x : ℝ × Z).2) : ℝ × ℝ).1 = 0 ∧
          0 ≤ 4 * Δ - (((x : ℝ × Z).1, Δ * edgeModelCore F (x : ℝ × Z).2) : ℝ × ℝ).2}) := by
  obtain ⟨δ₀, hδ₀, hrow⟩ := finiteSurface_edge_model_core_global o k hr hnorm hK hε hε1
  refine ⟨δ₀, hδ₀, fun z₀ q δ hδ hδ0 hq0 hqnn hdist hdense μ hμ hμ1 => ?_⟩
  obtain ⟨F, -, hFr, -, h, rfl, ⟨W, hW, hW9, hh⟩, -, -, -, hdisks, -, h4, -⟩ :=
    hrow z₀ q δ hδ hδ0 hq0 hqnn hdist hdense μ hμ hμ1
  obtain ⟨-, -, -, b, hb, hrange, -⟩ := hdisks 4 ⟨by norm_num, by norm_num⟩
  refine ⟨F, fun Δ hΔ => ⟨fun x => ?_, fun x => ?_, ?_⟩⟩
  · rw [← mul_sub, abs_mul, abs_of_pos hΔ, mul_comm]
    exact mul_lt_mul_of_pos_right (hFr x) hΔ
  · rw [mul_div_cancel_left₀ _ hΔ.ne']
    rfl
  · let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo
      (edgeModelCylinder_contMDiff_time (𝓡 2) z₀ Δ (edgeModelCore F))
      (edgeModelCylinder_contMDiff_height hW hW9 hh Δ (4 * Δ))
      (edgeModelCylinder_regular (𝓡 2) z₀ Δ (4 * Δ) (edgeModelCore F))
      (edgeModelCylinder_regular_boundary hW hW9 hh h4 hΔ)
    obtain ⟨⟨φ⟩, -, -, -⟩ := edgeModelCylinder_fibre_closedCell finrank_real_prod_euclideanTwo
      hW hW9 hh h4 hb hrange hΔ
    exact ⟨φ.toHomeomorph⟩

end DifferentialGeometry.Geometry.Collapse
