import DifferentialGeometry.Geometry.Fibration.ActualStageChainBases
import DifferentialGeometry.Geometry.Fibration.ActualStageChainERow

/-!
# GAF02 BASES: the final ordered row `gaf02_bases_row_BAS`

Blueprint `master207B.tex`, GAF02 (B:5797–5870); lead decision 11:1x (the final ordered row builds
`R` from GAF01's full choice and the three rough-graph rows, LAST group); D66-8; D71-13. The row is
GAF8b's producer `gaf02_chainE_row_GAF8` (ordered quantifiers verbatim) whose conclusion is
extended by the bases object `Gaf02Bases Ĉ.toChain Ĉ.rough` (`Gaf02ChainE.bases_BAS`, lane
C14-BASESc): the producer of the bases needs NO hypothesis besides the chain and its rough data, so
the row adds no threshold to register V4's slots.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The final ordered row of GAF02 BASES** (lead decision 11:1x; D66-8 "ONE register choice and
ONE bases object"): with GAF8b's ordered quantifiers verbatim (GAF01 moduli and CHOICE, weight
constants, first-stage thresholds, `β₂`, `Δ ≥ 1200` with the edge / slim thresholds, every packet of
the final family with the verbatim hypothesis list and `0 ≤ εr`, every base point `x₀`), the chain
`Ĉ : Gaf02ChainE` on the SAME choice carries the bases object `Gaf02Bases Ĉ.toChain Ĉ.rough` on its
OWN rough data (`R := Ĉ.rough`: TCP05 / EGP06 / SGP04 at `e_j` and GAF01's (OS)). No new
threshold is added to GAF8b's row. -/
theorem gaf02_bases_row_BAS (Kj : ℕ) {ν cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hcadj : 0 < cadj) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ) (c Γ S eg cw : Fin 3 → ℝ),
      (∀ j, 0 < θ j ∧ 0 < Γ j ∧ Γ j < θ j ∧ 0 < Ξ j (Γ j) ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξ j) (Γ j) ∧ 0 < S j ∧
        S j < Ξ j (Γ j) / 10000 ∧ 0 < eg j ∧ eg j < Γ j * S j / 100 ∧ 0 < c j ∧ 0 ≤ cw j) ∧
      c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧ c 2 < cadj ∧
      ∃ σ η₂ γ₀ ηc θt : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ 0 < η₂ ∧ 0 < γ₀ ∧ γ₀ ≤ 1 ∧ 0 < ηc ∧
        0 < θt ∧ θt < 1 ∧
      ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 →
      ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ Lc₁ η₀₁ θs Lc₂ η₀₂ : ℝ, 0 < η₁ ∧ 0 < Lc₁ ∧ 0 < η₀₁ ∧
        0 < θs ∧ θs < 1 ∧ 0 < Lc₂ ∧ 0 < η₀₂ ∧
      ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
        {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
        {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
        {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 → 3 * ν ≤ β 3 → β 3 < 1 →
        3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc → b ≤ η₁ → β 1 ≤ η₁ → 0 < σs →
        σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ → ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 →
        20 * Λz ≤ T → σ⁻¹ ≤ Lmax → 1000 * tcpGraphConst * Δ * Λ < eg 0 → b ≤ η₀₁ →
        s < 1 / 1000000 → β 1 ≤ η₀₁ → Lc₁ ≤ Lmax →
        σc ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg 1 / (20 * egpGraphConst) / 100 →
        σs ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → vs < eg 1 / (20 * egpGraphConst) / 100 →
        ζ ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg 1 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) → β 2 = β₂ → β 1 ≤ η₀₂ →
        Lc₂ ≤ Lmax → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 → ζ < θs ^ 2 / 10 ^ 6 →
        ζ < 1 / (100 * (1000000 * Δ)) → εr < θs / (100 * (1000000 * Δ)) → 0 ≤ εr →
        ∀ x₀ : X, ∃ C : Gaf02ChainE P Kj (fun j => Ξ j (Γ j)) Γ S eg c cw, C.x₀ = x₀ ∧
          Nonempty (Gaf02Bases C.toChain C.rough) := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, h1, h2, h3, h4, h5, h6,
    h7, h8, hrow⟩ := gaf02_chainE_row_GAF8 Kj hν hν1 hcadj
  refine ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, h1, h2, h3, h4, h5, h6,
    h7, h8, fun β₂ hβ₂ hβ₂1 Δ hΔ => ?_⟩
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, hrow'⟩ := hrow β₂ hβ₂ hβ₂1 Δ hΔ
  refine ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 x₀
  exact (hrow' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 x₀).elim fun C hC => ⟨C, hC, ⟨C.bases_BAS⟩⟩

end DifferentialGeometry.Geometry.Collapse
