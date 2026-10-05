import DifferentialGeometry.Geometry.Fibration.ActualConstantComparison

/-!
# Consumer of TCP03 (circle blocks): the strict `C¹` form with the native operator norm

* `opNorm_lt_of_pointwise_KA4`: a pointwise bound `‖F w‖ ≤ c √(R⁻² g(w, w))` with `c < θ` is an
  operator-norm bound `‖F‖ < θ` for the tangent norm of the bundle `R⁻² g`.
* `tcp03_circle_c1_lt`: TCP03's literal `‖s_j η_j − λ_j η_i‖_{C¹(D_i)} < θ` for every listed circle
  chart: value `< θ` and `‖s_j Dη_j − A_j Dη_i‖ < θ` in the operator norm of `ρ(i)⁻² g`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- A pointwise bound `‖F w‖ ≤ c √(R⁻² g(w, w))` with `0 ≤ c < θ` gives `‖F‖ < θ` for the tangent
norm of the bundle `R⁻² g`. -/
theorem opNorm_lt_of_pointwise_KA4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X) {R : ℝ} (hR : 0 < R)
    {x : X} {k : ℕ} (F : TangentSpace 𝓘(ℝ, E3) x →L[ℝ] EuclideanSpace ℝ (Fin k)) {c θ : ℝ}
    (hc : 0 ≤ c) (hcθ : c < θ) (hF : ∀ w, ‖F w‖ ≤ c * Real.sqrt (R⁻¹ ^ 2 * g.inner x w w)) :
    letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
    ‖F‖ < θ := by
  let _ := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  have hle : ‖F‖ ≤ c := by
    refine ContinuousLinearMap.opNorm_le_bound _ hc fun w => ?_
    have h := isMetricNorm_of_riemannianBundle (I := 𝓘(ℝ, E3)) (M := X)
      (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) x w
    rw [scaleMetric_inner, ← ofReal_norm] at h
    rw [(ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.sqrt_nonneg _)).mp h]
    exact hF w
  exact hle.trans_lt hcθ

/-- **TCP03 (circle blocks), literal `C¹` form**: for every listed circle chart `j` at a circle
centre `i`, one coisometry `A_j` with `|s_j η_j − λ_j(η_i)| < θ` on `D_i` and
`‖s_j Dη_j − A_j Dη_i‖ < θ` in the operator norm of `ρ(i)⁻² g`. -/
theorem tcp03_circle_c1_lt {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres) j (hj : j ∈ P.circle.centres),
        (tsupport (P.circle.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A : ℝ² →L[ℝ] ℝ², A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖(ρ j / ρ i) • cgpCircleCoord P.toLocalChartFamily j hj x -
                A (cgpCircleCoord P.toLocalChartFamily i hi x) -
                (ρ j / ρ i) • circleRaw_KA3 P j i‖ < θ ∧
            letI := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr (hρ i))
            ‖(ρ j / ρ i) • mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily j hj) x -
                A.comp (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x)‖ < θ := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, hrow⟩ := tcp03_circle_row hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hΔ
    hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hγ hσL i hi j hj hmeet
  obtain ⟨A, hA, -, htc⟩ := hrow P hΛ hΔ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hγ hσL i hi j hj
    hmeet
  refine ⟨A, hA, fun x hx => ⟨(htc x hx).1.trans_lt (by linarith), ?_⟩⟩
  exact opNorm_lt_of_pointwise_KA4 g (hρ i) _ (by linarith) (by linarith) (htc x hx).2

end DifferentialGeometry.Geometry.Collapse
