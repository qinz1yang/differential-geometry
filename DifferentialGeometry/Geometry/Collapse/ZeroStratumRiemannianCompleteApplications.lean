import DifferentialGeometry.Geometry.Collapse.ZeroStratumRiemannianComplete

/-!
# Consumers of the complete-manifold LC65/LC76 bindings and of LC65's explicit constants

* `exists_annular_exact_scale_strainer_explicit_constants`: LC65's metric kernel in the
  "choose θ first" order of the blueprint, with `δσ`, `Λσ` given by the blueprint's formulas in `σ`
  and the chosen `θ` (combines `exists_annularStrainer_blueprint_angle` and
  `annular_exact_scale_strainer_explicit`).
* `exists_line_unit_ball_splitting_parameter_riemannian_of_compact'`: the closed-manifold LC76
  statement recovered from the complete one (a metric on a compact manifold is complete).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v

/-- LC65 (metric kernel) in the blueprint's order of constants: for `0 < σ < 1` an angle
`0 < θ < π/2` is chosen first, and then `δσ`, `Λσ` are the blueprint's explicit formulas. -/
theorem exists_annular_exact_scale_strainer_explicit_constants {σ : ℝ} (hσ : 0 < σ)
    (hσone : σ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      ∀ {X C : Type*} [MetricSpace X] [MetricSpace C],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      ∀ (p : X) (o : C), RadialConeData o → ∀ {δ : ℝ}, KleinerLottApprox p o δ →
      δ < min ((1 / 10) / 60) (min (1 / (4 * 10 + 20)) ((1 / 10) * (1 - Real.cos θ) / 60)) →
      fourPointComparison ((1 / 60) ^ 2) (ball p 21) →
      ∀ q : X, 1 / 10 ≤ dist p q → dist p q ≤ 10 → ∀ lam : ℝ,
      max (2 * σ⁻¹ / (1 / 10)) (max ((1 / 60) / Real.sqrt σ) 2) ≤ lam →
      ∃ a b : X, dist q a = σ⁻¹ / lam ∧ dist q b = σ⁻¹ / lam ∧
        dist q a + dist a p = dist q p ∧
        Real.pi - σ < comparisonAngleNegCurvature σ (lam * dist q a) (lam * dist q b)
          (lam * dist a b) := by
  obtain ⟨θ, hθ, hθpi, hθside⟩ := exists_annularStrainer_blueprint_angle hσ hσone
  refine ⟨θ, hθ, hθpi, ?_⟩
  intro X C _ _ hsegments p o H δ φ hδ hcomp q hq1 hq2 lam hlam
  obtain ⟨a, b, -, -, -, -, hqa, hqb, hap, -, hangle⟩ :=
    annular_exact_scale_strainer_explicit hσ hσone hθ hθpi hθside hsegments p o H φ hδ hcomp
      q hq1 hq2 lam hlam
  exact ⟨a, b, hqa, hqb, hap, hangle⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- The closed-manifold LC76 statement, recovered from the complete-manifold binding. -/
theorem exists_line_unit_ball_splitting_parameter_riemannian_of_compact' {β : ℝ} (hβ : 0 < β)
    (hβone : β < 1) :
    ∃ δℓ Λℓ : ℝ, 0 < δℓ ∧ 0 < Λℓ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M) (p : M),
      (∀ y ∈ riemannianBallOf g p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      letI m := inducedMetricSpace g
      ∀ {δ o : ℝ}, KleinerLottApprox p o δ → δ < δℓ →
      ∀ q ∈ ball p 1, ∀ (lam : ℝ) (hlam : 0 < lam), Λℓ ≤ lam →
        @HasEuclideanSplitting.{u, 0} M (m.rescale lam hlam) q 1 β := by
  obtain ⟨δℓ, Λℓ, hδℓ, hΛℓ, hK⟩ :=
    exists_line_unit_ball_splitting_parameter_riemannian_of_complete.{u} (I := I) hβ hβone
  refine ⟨δℓ, Λℓ, hδℓ, hΛℓ, ?_⟩
  intro M _ _ _ _ _ _ _ g p hsec
  exact hK M g (riemannianMetricComplete_iff_inducedEMetricSpace.mpr
    (inducedEMetricSpace_completeSpace g)) p hsec

end DifferentialGeometry.Geometry.Collapse
