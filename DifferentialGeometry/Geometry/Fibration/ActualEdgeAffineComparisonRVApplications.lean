import DifferentialGeometry.Geometry.Fibration.ActualEdgeAffineComparisonRV

/-!
# Consumers of EGP04's row on the final family with LFR19's slim value tolerance

* `egp04_slim_at_centre`: on the thresholds of `egp04_row`, (EC) for a slim chart meeting `D_i`
  at the reference centre itself, where the translation is `c_j = s_j u_j(p_i)`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Consumer of `egp04_row`**: (EC) for a slim chart meeting `D_i`, at the reference centre
`p_i ∈ D_i`. -/
theorem egp04_slim_at_centre {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ)
        (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
          e T V vs),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 → 0 < σs → σs ≤ θ ^ 2 / 10 ^ 8 → vs < θ / 100 → ∀ i ∈ P.edge.centres,
          ∀ j (hj : j ∈ P.slim.centres),
            (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
            ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
              |ρ j / ρ i * (P.slim.centre j hj).coord i -
                  (a * P.edge.coord i i + ρ j / ρ i * sgpRaw P.slim j i)| < θ ∧
                ∀ w : TangentSpace 𝓘(ℝ, E3) i, (ρ i)⁻¹ ^ 2 * g.inner i w w = 1 →
                  |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord i w -
                    a * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) i w| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := egp04_row hΔ hβ₂ hβ₂1 hθ hθ1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs P hb hs
    hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs i hi j hj hmeet
  obtain ⟨-, hsl⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs P
    hb hs hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs i hi
  obtain ⟨a, ha, hEC⟩ := hsl j hj hmeet
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  exact ⟨a, ha, hEC i (mem_ball_self (by positivity))⟩

end DifferentialGeometry.Geometry.Collapse
