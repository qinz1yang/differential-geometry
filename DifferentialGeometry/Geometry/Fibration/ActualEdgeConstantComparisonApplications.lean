import DifferentialGeometry.Geometry.Fibration.ActualEdgeConstantComparison
import DifferentialGeometry.Geometry.Fibration.ActualConstantComparisonApplications

/-!
# Consumer of TCP03 (edge blocks): the strict `C¹` form with the native operator norm

* `tcp03_edge_c1_lt`: TCP03's literal `‖s_j η_j − λ_j η_i‖_{C¹(D_i)} < θ` for every listed edge
  chart (rank one as `t e₀`): value `< θ` and `‖s_j Dη_j e₀ − A_j Dη_i‖ < θ` in the operator norm
  of `ρ(i)⁻² g`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **TCP03 (edge blocks), literal `C¹` form**: for every listed edge chart `j` at a circle centre
`i`, one coisometry `A_j : ℝ² → ℝ¹` with `|s_j η_j e₀ − λ_j(η_i)| < θ` on `D_i` and
`‖s_j Dη_j e₀ − A_j Dη_i‖ < θ` in the operator norm of `ρ(i)⁻² g`. -/
theorem tcp03_edge_c1_lt {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ Δ : ℝ, 3 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → γ ≤ γ₀ → b ≤ η₁ → σc ≤ θ ^ 2 / 1000 →
      μ * Δ ≤ θ / 100 → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres), ∀ j ∈ P.edge.centres,
        (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A : ℝ² →L[ℝ] ℝ¹, A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖(ρ j / ρ i) • EuclideanSpace.single 0 (P.edge.coord j x) -
                A (cgpCircleCoord P.toLocalChartFamily i hi x) -
                (ρ j / ρ i) • EuclideanSpace.single 0 (edgeRaw_KA3 P.toLocalChartFamily j i)‖ < θ ∧
            letI := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr (hρ i))
            ‖(ρ j / ρ i) • (mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x).smulRight
                  (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) -
                A.comp (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x)‖ < θ := by
  obtain ⟨σ, hσ, hσ1, γ₀, hγ₀, hrow⟩ := tcp03_edge_row hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, γ₀, hγ₀, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hrow'⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hμ hτ
    hLΛ hLmax he hT hν3 hβ3 hβ2σ hγ hb hσc hμΔ hσL i hi j hj hmeet
  obtain ⟨A, hA, -, htc⟩ := hrow' P hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hγ hb hσc hμΔ hσL i hi
    j hj hmeet
  refine ⟨A, hA, fun x hx => ⟨(htc x hx).1.trans_lt (by linarith), ?_⟩⟩
  refine opNorm_lt_of_pointwise_KA4 g (hρ i) _ (c := θ / 2) (by linarith) (by linarith) fun w => ?_
  have h := (htc x hx).2 w
  rw [sub_apply, smul_apply]
  convert h using 4
  · ext k
    fin_cases k
    simp
  · rfl

end DifferentialGeometry.Geometry.Collapse
