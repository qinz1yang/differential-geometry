import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopSgpRows
import DifferentialGeometry.Geometry.Fibration.ActualSlimRankApplications

/-!
# SGP04, SGP05 and SGP06 on ONE threshold triple (S-FIXTURE-C2d, G8 file 1)

`loopSgp456_FXC2` extends `loopSgp46_FXC2` (SphereLoopSgpRows.lean) by the conclusion of
`sgp05_row_C14` (ActualSlimRankApplications.lean), VERBATIM: for every `Δ ≥ 1`, `β₂ ∈ (0, 1)` and
admissible accuracy parameters there is ONE triple `(θ, L_c, η)` (`θ = min`, `L_c = sum`,
`η = min` of the thresholds of the three rows) under which the SGP04 `Sgp04OutV2`, the SGP06
`Sgp06OutV2` and the SGP05 projected-rank conclusion (copied from `sgp05_row_C14`, the
graph accuracy `eg` of SGP04 is also the accuracy of SGP05) hold on every `LocalChartPacketsC14`.
The tree has no packaged `Out` for SGP05, so its conclusion is written out here.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter GC.MetricGeometry
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Analysis

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **SGP04, SGP05 and SGP06 on one threshold triple.** -/
theorem loopSgp456_FXC2 {Δ β₂ eg Γ sg eg₆ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
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
        Sgp04OutV2 P.toLocalChartPacketsRVZ eg ∧ Sgp06OutV2 P Γ sg eg₆ ∧
        ∀ i : P.toLocalChartFamily.slim.finite_centres.toFinset, ∃ sgn c zsgn zc : X → ℝ,
          (∀ j, |sgn j| ≤ 1) ∧ (∀ k, |zsgn k| ≤ 1) ∧
          (∀ x ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x| ≤
              8 * 10 ^ 5 * Δ →
            ‖(ρ i.1)⁻¹ • cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero) x -
              sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc
                ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)‖ < eg ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x,
              ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                  (cgpQ3Tags P.toLocalChartFamily P.zero)) x w -
                fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
                  ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord x)
                  (mvfderiv 𝓘(ℝ, E3) (P.slim.centre i.1
                    ((Set.Finite.mem_toFinset _).mp i.2)).coord x w)‖ ≤
                eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner x w w)) ∧
          ∀ p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1),
            |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
              7 * (10 ^ 5 * Δ) →
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) p →
            let Tx := fderiv ℝ (sgpFullGraph P.toLocalChartFamily P.zero i sgn c zsgn zc)
              ((P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p)
            let Pq := Tx.range.orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) := by
  have h46 := loopSgp46_FXC2 hΔ hβ₂ hβ₂1 heg heg1 hΓ hΓ1 hsg hsgΓ hsgC heg6 heg61 hegΓ
  obtain ⟨θ₄, Lc₄, η₄, hθ₄, hLc₄, hη₄, h4⟩ := h46
  have h5 := sgp05_row_C14 hΔ hβ₂ hβ₂1 heg heg1
  obtain ⟨θ₅, hθ₅, hθ₅1, Lc₅, η₅, hLc₅, hη₅, h5⟩ := h5
  refine ⟨min θ₄ θ₅, Lc₄ + Lc₅, min η₄ η₅, lt_min hθ₄ hθ₅, add_pos hLc₄ hLc₅, lt_min hη₄ hη₅, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ hη hL hΛ hΛΔ he hT hΛz hσs hσ hv hζ hζ1 hζ2 hεr
  have hθ : 0 < min θ₄ θ₅ := lt_min hθ₄ hθ₅
  have hq : (0 : ℝ) < 100 * (1000000 * Δ) := by positivity
  have hr4 : εr < θ₄ / (100 * (1000000 * Δ)) :=
    hεr.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) hq.le)
  have hr5 : εr < θ₅ / (100 * (1000000 * Δ)) :=
    hεr.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) hq.le)
  have hS4 := h4 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hβ
    (hη.trans (min_le_left _ _)) (by linarith) hΛ hΛΔ he hT hΛz hσs
    (loopSqMono_FXC2 hθ (min_le_left _ _) hσ) (loopLinMono_FXC2 (min_le_left _ _) hv) hζ
    (loopSqMono_FXC2 hθ (min_le_left _ _) hζ1) hζ2 hr4
  have hS5 := h5 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P hβ
    (hη.trans (min_le_right _ _)) (by linarith) hΛ hΛΔ he hT hΛz hσs
    (loopSqMono_FXC2 hθ (min_le_right _ _) hσ) (loopLinMono_FXC2 (min_le_right _ _) hv) hζ
    (loopSqMono_FXC2 hθ (min_le_right _ _) hζ1) hζ2 hr5
  exact ⟨hS4.1, hS4.2, hS5⟩

end DifferentialGeometry.Geometry.Collapse
