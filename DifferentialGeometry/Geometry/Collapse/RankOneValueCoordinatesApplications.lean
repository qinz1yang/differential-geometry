import DifferentialGeometry.Geometry.Collapse.RankOneValueCoordinates

/-!
# Consumers of LFR19

* `rankOne_coordinate_derivative_lower`: on a fixed complete smooth manifold, the LFR19
  coordinate has derivative at least `1 - κ - σ` along every minimizing direction of a tested
  segment whose coordinate slope is at least `1 - κ` (the form used in LFR20.1 and in the
  tangential half of LFR36.2).
* `exists_edge_tangential_coordinate`: LFR19 with the LFR36 parameters `L = 100Δ`,
  `T = 1000Δ`, value error `μΔ`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- The LFR19 coordinate has derivative at least `1 - κ - σ` along every minimizing direction
of a tested segment of coordinate slope at least `1 - κ`. -/
theorem rankOne_coordinate_derivative_lower (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {Y : Type*} [MetricSpace Y] (p : M) (y₀ : Y)
    {L T e σ : ℝ} (hL : 0 < L) (hT : 2 * L < T) (he : 0 < e) (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β,
      (∀ y ∈ Metric.ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      ∃ η : M → ℝ, η p = 0 ∧ (∀ x ∈ Metric.ball p L, |η x - (α.toFun x).fst| < e) ∧
        ∀ x ∈ Metric.ball p L, ∀ x' ∈ Metric.ball p T, L < dist x x' →
          ∀ w : TangentSpace I x, g.inner x w w = 1 →
          intrinsicGeodesic g hEnorm x w (dist x x') = x' → ∀ κ : ℝ,
          1 - κ ≤ ((α.toFun x').fst - (α.toFun x).fst) / dist x x' →
          1 - κ - σ < mvfderiv (I := I) η x w := by
  obtain ⟨β₀, hβ₀, hcoord⟩ := exists_rankOne_coordinate_value_tolerance hL hT he hσ hσone
  refine ⟨β₀, hβ₀, fun β hβ hβsmall α hsec => ?_⟩
  obtain ⟨η, -, -, -, -, hηp, -, hvalue, -, -, htest⟩ :=
    hcoord β hβ hβsmall E H I M g hEnorm Y p y₀ α hsec
  refine ⟨η, hηp, hvalue, fun x hx x' hx' hxx' w hw hwx' κ hκ => ?_⟩
  have h := (abs_lt.mp (htest x hx x' hx' hxx' w hw hwx')).1
  linarith

universe uE uH u v

/-- LFR19 with the parameters of LFR36: `L = 100Δ`, `T = 1000Δ`, value error `μΔ`, quality
`σ`. -/
theorem exists_edge_tangential_coordinate {Δ μ σ : ℝ} (hΔ : 1 ≤ Δ) (hμ : 0 < μ)
    (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (Y : Type v) [MetricSpace Y] (p : M) (y₀ : Y)
        (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y ∈ Metric.ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∃ f : M → ℝ, ∃ O : Set M, IsOpen O ∧ Metric.closedBall p (100 * Δ) ⊆ O ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f O ∧ f p = 0 ∧
          LipschitzWith (Real.toNNReal (1 + σ)) f ∧
          (∀ x ∈ Metric.ball p (100 * Δ), |f x - (α.toFun x).fst| < μ * Δ) ∧
          ∀ x ∈ Metric.ball p (100 * Δ), ∀ x' ∈ Metric.ball p (1000 * Δ),
            100 * Δ < dist x x' →
            ∀ w : TangentSpace I x, g.inner x w w = 1 →
            intrinsicGeodesic g hEnorm x w (dist x x') = x' →
            |mvfderiv (I := I) f x w -
              ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ := by
  obtain ⟨β₀, hβ₀, hcoord⟩ := exists_rankOne_coordinate_value_tolerance.{uE, uH, u, v}
    (by linarith : (0 : ℝ) < 100 * Δ) (by linarith : 2 * (100 * Δ) < 1000 * Δ)
    (by positivity : 0 < μ * Δ) hσ hσone
  refine ⟨β₀, hβ₀, fun β hβ hβsmall E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Y _ p y₀ α
    hsec => ?_⟩
  obtain ⟨f, O, hO, hCO, hf, hfp, hfl, hvalue, -, -, htest⟩ :=
    hcoord β hβ hβsmall E H I M g hEnorm Y p y₀ α hsec
  exact ⟨f, O, hO, hCO, hf, hfp, hfl, hvalue, htest⟩

end DifferentialGeometry.Geometry.Collapse
