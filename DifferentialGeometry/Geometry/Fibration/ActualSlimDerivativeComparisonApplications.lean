import DifferentialGeometry.Geometry.Fibration.ActualSlimDerivativeComparison

/-!
# Consumer of SGP03: (SC) wherever the actual OR the model `j` cutoff is positive

Blueprint `master207B.tex`, SGP03 (B:4500): "Thus (SC) applies whenever the actual OR model `j`
cutoff is positive." On the thresholds of `sgp03_row`: at `x ∈ D_i` where the actual slim cutoff
`P.slim.cutoff j` or the model cutoff `f(λ_j(η_i)/(s_jℓ))` is nonzero, `x ∈ B(j, Lρ(j))`, so the
derivative and value bounds of (SC) hold at `x` (`sgp03_sc_of_cutoff_ne_zero`).
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **(SC) where either `j` cutoff is positive** (SGP03, last sentence of the statement), on the
thresholds of `sgp03_row`. -/
theorem sgp03_sc_of_cutoff_ne_zero {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) (hEθ : E < θ ^ 2 / 10 ^ 6) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ)
        (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
          e T V vs),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        ∀ i (hi : i ∈ P.slim.centres), ∀ j (hj : j ∈ sgpSlimList P.slim i), ∃ a : ℝ,
          (a = 1 ∨ a = -1) ∧
          ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
            (P.slim.cutoff j x ≠ 0 ∨
              slimCutoffProfile_LC87 ((a * (P.slim.centre i hi).coord x +
                ρ j / ρ i * sgpRaw P.slim j i) / (ρ j / ρ i * (100000 * Δ))) ≠ 0) →
            (∀ w : TangentSpace 𝓘(ℝ, E3) x,
              |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj.1).coord x w -
                a * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) ∧
            |ρ j / ρ i * (P.slim.centre j hj.1).coord x -
              (a * (P.slim.centre i hi).coord x + ρ j / ρ i * sgpRaw P.slim j i)| < θ := by
  obtain ⟨Lc, η₀, hLc, hη₀, h⟩ := sgp03_row hΔ hβ₂ hβ₂1 hθ hθ1 hE hEθ
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs P hβ2
    hβ1 hLmax hΛ hLΛ hσs hσθ hvθ i hi j hj
  obtain ⟨a, ha, -, hD, hM, hV⟩ := h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
    e T V vs P hβ2 hβ1 hLmax hΛ hLΛ hσs hσθ hvθ i hi j hj
  refine ⟨a, ha, fun x hxi hcut => ?_⟩
  have hrj := hρ j
  have hΔ0 : 0 < Δ := by linarith
  have hxj : x ∈ ball j (1000000 * Δ * ρ j) := by
    rcases hcut with hc | hc
    · have hc' : (P.slim.centre j hj.1).cutoff x ≠ 0 := by
        unfold SlimFamily.cutoff at hc
        rwa [dite_eq_left hj.1] at hc
      have hx := (P.slim.centre j hj.1).tsupport_cutoff_subset (subset_tsupport _ hc')
      rw [mem_closedBall] at hx
      rw [mem_ball]
      have hlt : 91 / 100 * (10 ^ 6 * Δ) * ρ j < 1000000 * Δ * ρ j := by
        have : 0 < Δ * ρ j := mul_pos hΔ0 hrj
        nlinarith
      linarith
    · have hx := hM x hxi hc
      refine ball_subset_ball ?_ hx
      have : 0 < Δ * ρ j := mul_pos hΔ0 hrj
      nlinarith
  exact ⟨hD x hxi hxj, hV x hxi hxj⟩

end DifferentialGeometry.Geometry.Collapse
