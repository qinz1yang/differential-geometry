import DifferentialGeometry.Geometry.Comparison.FiniteSoul.StrictConvexBall
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.ShortInterpolation

/-!
# Consumers of S-CVX and of the short geodesic interpolation

* `exists_strictConvex_radius_of_C3`: strictly convex balls for a complete `C³` metric (`r = 2`).
* `exists_shortInterpolation_midpoint_chart_of_C3`: the chart reading of the short geodesic
  midpoint `J(x, y, 1/2)` of a `C³` metric has derivative `(fst + snd)/2` at the diagonal.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Strictly convex balls for a complete `C³` metric. -/
theorem exists_strictConvex_radius_of_C3
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I (((2 : ℕ∞) : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ → ℓ ≤ 2 * ρ →
      g.inner p.proj p.snd p.snd = 1 → dist x p.proj ≤ ρ → dist x (g.geodesicFlow p ℓ).proj ≤ ρ →
      StrictConvexOn ℝ (Icc 0 ℓ) (fun t => dist x (g.geodesicFlow p t).proj ^ 2) ∧
        ∀ t ∈ Icc 0 ℓ, dist x (g.geodesicFlow p t).proj ≤ ρ :=
  exists_strictConvex_radius g le_rfl hnorm hK

/-- The short geodesic midpoint of a `C³` metric, read in the chart at `x₀`, has derivative
`(fst + snd)/2` at `(κ x₀, κ x₀)`. -/
theorem exists_shortInterpolation_midpoint_chart_of_C3
    (g : ContMDiffRiemannianMetric I (((2 : ℕ∞) : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (x₀ : M) :
    ∃ W : Set (E × E), IsOpen W ∧ ((extChartAt I x₀ x₀, extChartAt I x₀ x₀) : E × E) ∈ W ∧
      ∃ L : E × E → E,
        (∀ z ∈ W, g.expMap (⟨(extChartAt I x₀).symm z.1,
          mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M) =
            (extChartAt I x₀).symm z.2) ∧
        HasFDerivAt (fun z : E × E => extChartAt I x₀
          (g.expMap (⟨(extChartAt I x₀).symm z.1,
            (1 / 2 : ℝ) • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm z.1 (L z)⟩ : TangentBundle I M)))
          ((1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))
          (extChartAt I x₀ x₀, extChartAt I x₀ x₀) := by
  obtain ⟨W, hWo, hw₀, -, L, -, -, -, -, hexp, -, -, hder⟩ :=
    Bundle.ContMDiffRiemannianMetric.exists_shortInterpolation_chart g (r := 2) one_le_two x₀
  refine ⟨W, hWo, hw₀, L, hexp, ?_⟩
  have h := hder (1 / 2)
  have hcoef : (1 - 1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ E E +
      (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ E E =
      (1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) := by
    rw [smul_add]
    norm_num
  rwa [hcoef] at h

end DifferentialGeometry.Geometry.FiniteSoul
