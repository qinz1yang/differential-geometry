import DifferentialGeometry.Geometry.Collapse.EdgeReferenceChartUniform

/-!
# Consumer: the LFR35 anchors are as accurate as any later choice demands

With the real numerical values `γ = 1/1000`, `β₂ = 10⁻⁷`, `ι = 1/100` of the row: for every
`Δ ≥ Δ₀` and every prescribed `δ > 0` one coarse tolerance `τ` with `τΔ < δ` works, and the
SAME smooth chart then has its anchors `δ`-accurate, vanishes at the centre and is `γ`-close to
the actual comparison map on the radius-`100q` ball.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe uE uH uM

/-- The anchors of the row's reference chart can be certified to any accuracy `δ`. -/
theorem edgeReference_anchor_error_arbitrarily_small :
    ∃ Δ₀ > 1, ∀ Δ, Δ₀ ≤ Δ → ∀ δ > 0, ∃ τ > 0, τ * Δ < δ ∧ ∃ κ > 0,
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (_ : IsMetricNorm (I := I) g)
        (Q : M → WithLp 2 (ℝ × ℝ)) (p : M) (A : Set M),
      (∀ y ∈ ball p (10000 * Δ), SectionalBoundedBelowAt g y (-κ ^ 2)) →
      Q p = 0 →
      (∀ y ∈ ball p (200 * Δ), ∀ z ∈ ball p (200 * Δ),
        |dist (Q y) (Q z) - dist y z| ≤ τ * Δ) →
      (∀ y ∈ ball p (200 * Δ), 0 ≤ (Q y).snd) →
      (∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ y ∈ ball p (200 * Δ), dist (Q y) z ≤ τ * Δ) →
      p ∈ A → (∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ) →
      (∀ t : ℝ, |t| ≤ 100 * Δ → ∃ a ∈ A ∩ ball p (190 * Δ),
        dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ) →
      ∀ x, x ∈ ball p (15 * Δ) → 9 / 100 * Δ ≤ infDist x A →
        infDist x A ≤ 101 / 10 * Δ →
      ∃ anchors : Fin 2 → M, ∃ χ : M → EuclideanSpace ℝ (Fin 2),
        (∀ j, dist (Q (anchors j)) (Q x + planeReferenceIsometry.symm
            (EuclideanSpace.single j (Δ / 40))) < δ) ∧
        χ x = 0 ∧
        ∀ y ∈ ball x 100,
          ‖χ y - planeReferenceIsometry (planeComparisonMap Q p x Δ 1 y)‖ < 1 / 1000 := by
  obtain ⟨Δ₀, hΔ₀, hrow⟩ := exists_edge_reference_chart_parameters_uniform.{uE, uH, uM}
    (β := 1 / 10000000) (γ := 1 / 1000) (ι := 1 / 100) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Δ₀, hΔ₀, fun Δ hΔ δ hδ => ?_⟩
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨τ₀, hτ₀, κ, hκ, hτ⟩ := hrow Δ hΔ
  let τ := min τ₀ (δ / (2 * Δ))
  have hτpos : 0 < τ := lt_min hτ₀ (by positivity)
  have hτΔ : τ * Δ < δ := by
    have hh : τ ≤ δ / (2 * Δ) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at hh
    linarith
  refine ⟨τ, hτpos, hτΔ, κ, hκ, ?_⟩
  intro E _ _ _ _ H _ I _ M _ _ _ _ _ _ _ _ g hEnorm Q p A hsec hQp hdist hheight hcover hpA
    hborder hbordercover x hx hxA hxA'
  obtain ⟨anchors, χ, hanchors, -, hχ0, -, -, -, -, -, -, -, -, hclose, -⟩ :=
    hτ τ (min_le_left _ _) E H I M g hEnorm Q p A hsec hQp hdist hheight hcover hpA hborder
      hbordercover x hx hxA hxA' 1 (by norm_num) (by norm_num)
  exact ⟨anchors, χ, fun j => (hanchors j).2.trans_lt hτΔ, hχ0,
    fun y hy => hclose y (by simpa only [mul_one] using hy)⟩

end DifferentialGeometry.Geometry.Collapse
