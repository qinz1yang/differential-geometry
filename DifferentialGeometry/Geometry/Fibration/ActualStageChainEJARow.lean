import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJA
import DifferentialGeometry.Geometry.Fibration.ActualStageChainERow

/-!
# The producer of `Gaf02ChainEJA` (GAF01's (JA) on the same choice, D66-2 order)

Blueprint `master207B.tex`, GAF01 (B:5705–5711, (JA): `Σ_j ≤ ε_j/10000`,
`c₃ < min{c_adjust, 1/1000, 1/512}`) and GAF02 (B:5797); review 66, D66-2 / D66-3 / D66-6.

`gaf02_chainEJA_row_GAFC Kj` has the quantifier order and the hypothesis list of
`gaf02_chainE_row_GAF8` verbatim (GAF01 moduli and CHOICE with `c₃ < c_adj`, the weight constants,
the first-stage thresholds, THEN `β₂`, THEN `Δ ≥ 1200` and the edge / slim thresholds, then every
packet of the final family with `0 ≤ εr`, every base point `x₀`); its conclusion is the chain WITH
(JA): `∃ Ĉ : Gaf02ChainEJA … cadj, Ĉ.x₀ = x₀`.

Proof: ONE call of `gaf02_chainE_row_GAF8` at the early target `min c_adj (1/1000)`. Its single
numeric choice (`gaf02_chain_choice_full_GAF8`, i.e. GAF01's CHOICE) gives
`c₃ < min c_adj (1/1000)`, which is the `c₃`-part of (JA); the chain `Ĉ` it returns on the given
packet (enhanced planes → native outputs with plane slot `A_j.plane` → chain → ChoiceValidity) is
wrapped with these two inequalities. No second existence call, no number chosen after the family.
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAFCR {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAFCR {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAFCR {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF02 CORE on the enhanced planes with GAF01's (JA): the producer** (D66-2 order, ordered
quantifiers of `gaf02_chainE_row_GAF8`). GAF01's shared moduli `θ, Ξ` and its CHOICE `c, Γ, Σ, e`
with `c₃ < c_adj`, the weight constants `c_w`, the first-stage thresholds, for every
`β₂ ∈ (0, 10⁻⁶)` and `Δ ≥ 1200` the edge / slim thresholds; then on every packet of the final
family with the verbatim hypothesis list and `0 ≤ εr` (D66-6), for every base point `x₀`, a chain
`Ĉ : Gaf02ChainEJA … c_adj` on the SAME choice: `Ĉ.toGaf02ChainE` is `gaf02_chainE_row_GAF8`'s chain
and `Ĉ.c_lt_adj`, `Ĉ.c_two_lt` are the `c₃`-part of (JA). -/
theorem gaf02_chainEJA_row_GAFC (Kj : ℕ) {ν cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1)
    (hcadj : 0 < cadj) :
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
        ∀ x₀ : X, ∃ C : Gaf02ChainEJA P Kj (fun j => Ξ j (Γ j)) Γ S eg c cw cadj, C.x₀ = x₀ := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, hrow⟩ := gaf02_chainE_row_GAF8 Kj hν hν1 (cadj := min cadj (1 / 1000))
      (lt_min hcadj (by norm_num))
  have hca : c 2 < cadj := hc2.trans_le (min_le_left _ _)
  have hc1000 : c 2 < 1 / 1000 := hc2.trans_le (min_le_right _ _)
  refine ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hca, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, fun β₂ hβ₂ hβ₂1 Δ hΔ => ?_⟩
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, hrow'⟩ := hrow β₂ hβ₂ hβ₂1 Δ hΔ
  refine ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
    f27 f28 f29 f30 f31 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5 m6 m7 m8 hεr0 x₀
  obtain ⟨C, hC⟩ := hrow' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20
    f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5 m6
    m7 m8 hεr0 x₀
  exact ⟨{ C with c_lt_adj := hca, c_two_lt := hc1000 }, hC⟩

end DifferentialGeometry.Geometry.Collapse
