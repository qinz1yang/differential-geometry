import DifferentialGeometry.Geometry.Fibration.ActualHeightComparison
import DifferentialGeometry.Geometry.Fibration.ActualConstantComparisonApplications

/-!
# Consumer of TCP04: the strict `C¹` form of the high branch with the native operator norm

* `tcp04_high_c1_lt`: at a circle centre whose `D_i` meets an edge support and where the LOW
  branch fails at some point of `D_i`, one unit row `B` with `‖(t − t(p_i)) e₀ − B(η_i − η_i(p_i))‖ < θ`
  and `‖dt e₀ − B Dη_i‖ < θ`, `‖dt‖ < 3` in the operator norm of `ρ(i)⁻² g` on `D_i`.
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

/-- **TCP04, high branch in literal `C¹` form**: under `tcp04_row`'s thresholds, at a circle centre
`i` whose `D_i` meets an edge support and contains a point with `t ≥ 3Δ/20`, one unit row
`B : ℝ² → ℝ¹` with, on `D_i`, `‖(t − t(p_i)) e₀ − B(η_i − η_i(p_i))‖ < θ`, and
`‖dt e₀ − B Dη_i‖ < θ`, `‖dt e₀‖ < 3` in the operator norm of `ρ(i)⁻² g`. -/
theorem tcp04_high_c1_lt {θ ν : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ ηc : ℝ, 0 < ηc ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
      (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
        V),
      0 ≤ Λ → 1200 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ 1 → 3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ →
      γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc → σ⁻¹ ≤ Lmax →
      ∀ i (hi : i ∈ P.circle.centres),
        (∃ j ∈ P.edge.centres, (tsupport (P.edge.cutoff j) ∩ ball i (10 * ρ i)).Nonempty) →
        (∃ x ∈ ball i (10 * ρ i), 3 * Δ / 20 ≤ P.edge.smoothing x / ρ x) →
        ∃ B : ℝ² →L[ℝ] ℝ¹, B.comp (ContinuousLinearMap.adjoint B) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x ∈ ball i (10 * ρ i),
            ‖EuclideanSpace.single 0 (P.edge.smoothing x / ρ x - P.edge.smoothing i / ρ i) -
                B (cgpCircleCoord P.toLocalChartFamily i hi x -
                  cgpCircleCoord P.toLocalChartFamily i hi i)‖ < θ ∧
            letI := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr (hρ i))
            ‖(mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x).smulRight
                  (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) -
                B.comp (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord P.toLocalChartFamily i hi) x)‖ < θ ∧
            ‖(mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x).smulRight
                  (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))‖ < 3 := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, ηc, hηc, hrow⟩ := tcp04_row hθ hθ1 hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, γ₀, hγ₀, ηc, hηc, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V P hΛ hΔ
    hμ hτ hLΛ hLmax he hT hε hε1 hσc0 hσc1 hν3 hβ3 hβ2σ hβ2 hγ hγc hγcθ hβc hσL i hi hmeet
    ⟨x₀, hx₀, hx₀t⟩
  rcases (hrow P hΛ hΔ hμ hτ hLΛ hLmax he hT hε hε1 hσc0 hσc1 hν3 hβ3 hβ2σ hβ2 hγ hγc hγcθ hβc
    hσL i hi).2 hmeet with hlow | ⟨B, hB, hhigh⟩
  · exact absurd (hlow x₀ hx₀).1 (not_lt.mpr hx₀t)
  refine ⟨B, hB, fun x hx => ⟨(hhigh x hx).2.2.2.1.trans_lt (by linarith), ?_, ?_⟩⟩
  · refine opNorm_lt_of_pointwise_KA4 g (hρ i) _ (c := θ / 20) (by positivity) (by linarith)
      fun w => ?_
    have h := ((hhigh x hx).2.2.2.2 w).1
    rw [sub_apply]
    convert h using 3
    · ext k
      fin_cases k
      simp
    · rfl
  · refine opNorm_lt_of_pointwise_KA4 g (hρ i) _ (c := 2) (by norm_num) (by norm_num) fun w => ?_
    have h := ((hhigh x hx).2.2.2.2 w).2
    have e : ((mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x).smulRight
        (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) w =
        EuclideanSpace.single 0 (mvfderiv 𝓘(ℝ, E3) (fun y => P.edge.smoothing y / ρ y) x w) := by
      ext k
      fin_cases k
      simp
    rw [e, PiLp.norm_single, Real.norm_eq_abs]
    exact h

end DifferentialGeometry.Geometry.Collapse
