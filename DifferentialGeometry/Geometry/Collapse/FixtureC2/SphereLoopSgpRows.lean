import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopRowsRegister
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV2BranchOuts

/-!
# SGP04 and SGP06 on ONE threshold triple (S-FIXTURE-C2c, R2, G6 file 2)

`loopSgp46_FXC2`: the graph rows `sgp04_row_out_VAL3` (as `Sgp04OutV2`) and `sgp06_row_C14_out_VAL3`
(as `Sgp06OutV2`) have their own thresholds `(θ, L_c, η₀)`; for every `Δ ≥ 1`, `β₂ ∈ (0, 1)` and
every admissible accuracy parameters there is ONE triple `(θ, L_c, η)` (`θ = min`, `L_c = sum`,
`η = min`) under which BOTH conclusions hold on every `LocalChartPacketsC14`. This is the form
in which the two rows join the register of the chain row on a fixture packet.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **SGP04 and SGP06 on one threshold triple.** -/
theorem loopSgp46_FXC2 {Δ β₂ eg Γ sg eg₆ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (heg : 0 < eg) (heg1 : eg < 1 / 100) (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg6 : 0 < eg₆)
    (heg61 : eg₆ < 1 / 100) (hegΓ : eg₆ < Γ * sg / 100) :
    ∃ θ Lc η : ℝ, 0 < θ ∧ 0 < Lc ∧ 0 < η ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        Sgp04OutV2 P.toLocalChartPacketsRVZ eg ∧ Sgp06OutV2 P Γ sg eg₆ := by
  have h4 := sgp04_row_out_VAL3 hΔ hβ₂ hβ₂1 heg heg1
  obtain ⟨θ₄, hθ₄, hθ₄1, Lc₄, η₄, hLc₄, hη₄, h4⟩ := h4
  have h6 := sgp06_row_C14_out_VAL3 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg6 heg61 hegΓ
  obtain ⟨θ₆, hθ₆, hθ₆1, Lc₆, η₆, hLc₆, hη₆, h6⟩ := h6
  refine ⟨min θ₄ θ₆, Lc₄ + Lc₆, min η₄ η₆, lt_min hθ₄ hθ₆, add_pos hLc₄ hLc₆, lt_min hη₄ hη₆, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ hη hL hΛ hΛΔ he hT hΛz hσs hσ hv hζ hζ1 hζ2 hεr
  have hθ : 0 < min θ₄ θ₆ := lt_min hθ₄ hθ₆
  have hq : (0 : ℝ) < 100 * (1000000 * Δ) := by positivity
  have hr4 : εr < θ₄ / (100 * (1000000 * Δ)) :=
    hεr.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) hq.le)
  have hr6 : εr < θ₆ / (100 * (1000000 * Δ)) :=
    hεr.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) hq.le)
  exact ⟨h4 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      P.toLocalChartPacketsRVZ hβ (hη.trans (min_le_left _ _)) (by linarith) hΛ hΛΔ he hT hΛz
      hσs (loopSqMono_FXC2 hθ (min_le_left _ _) hσ)
      (loopLinMono_FXC2 (min_le_left _ _) hv) hζ (loopSqMono_FXC2 hθ (min_le_left _ _) hζ1) hζ2 hr4,
    h6 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hβ
      (hη.trans (min_le_right _ _)) (by linarith) hΛ hΛΔ he hT hΛz hσs
      (loopSqMono_FXC2 hθ (min_le_right _ _) hσ) (loopLinMono_FXC2 (min_le_right _ _) hv) hζ
      (loopSqMono_FXC2 hθ (min_le_right _ _) hζ1) hζ2 hr6⟩

end DifferentialGeometry.Geometry.Collapse
