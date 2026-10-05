import DifferentialGeometry.Geometry.Fibration.ActualEdgeAffineComparison

/-!
# Consumers of EGP04's edge tier on the actual family

* `egp04_edge_at_centre`: on the same thresholds, (EC) at the reference centre itself, where the
  translation is `c_j = s_j u_j(p_i)`.
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

/-- **Consumer of `egp04_edge`**: (EC) at the reference centre `p_i ∈ D_i`. -/
theorem egp04_edge_at_centre {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ : ℝ)
        (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 → ∀ i ∈ L.edge.centres, ∀ j ∈ egpEdgeList L.toLocalChartFamily i,
          ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            |ρ j / ρ i * L.edge.coord j i -
                (a * L.edge.coord i i + ρ j / ρ i * egpRaw L.edge j i)| < θ ∧
              ∀ w : TangentSpace 𝓘(ℝ, E3) i, (ρ i)⁻¹ ^ 2 * g.inner i w w = 1 →
                |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (L.edge.coord j) i w -
                  a * mvfderiv 𝓘(ℝ, E3) (L.edge.coord i) i w| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := egp04_edge hΔ hβ₂ hβ₂1 hθ hθ1
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1 hLmax hΛ
    hLΛ hμ hτ hσc hμΔ i hi j hj
  obtain ⟨a, ha, hEC⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ L hb hs hβ1
    hLmax hΛ hLΛ hμ hτ hσc hμΔ i hi j hj
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  exact ⟨a, ha, hEC i (mem_ball_self (by positivity))⟩

end DifferentialGeometry.Geometry.Collapse
