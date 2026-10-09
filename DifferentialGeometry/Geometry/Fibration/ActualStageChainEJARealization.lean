import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJARow
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdp01
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# EDP01 on `Gaf02ChainE` and the realization wrapper on the final family (D66-6)

Blueprint `master207B.tex`, EDP01 (B:6666–6735) and GAF02 (B:5797); review 66, D66-3 (EDP01's
numeric needs `Σ₁ ≤ ε₁/10000`, `0 ≤ c_w` travel in the ChoiceValidity record) and D66-6 (`0 ≤ εr` is
kept explicit on the row; the realization wrapper discharges it from the final-family producer's
`0 < εr`, with no reorder and no new small quantity).

* `Gaf02ChainE.edp01_GAFC`: EDP01's (SD) for the scale `s = ℓ_ρ(E)` of a chain on the enhanced
  planes, with `C_ρ = 100(L₀ + 1)(1 + b_cut + c_w(1)/Σ₁) ≥ 100`, `s` differentiable and positive —
  NO hypothesis: `0 ≤ c_w(1)` and `Σ₁ ≤ ε₁/10⁴` are the record's `cw_nonneg 0`, `sigma_le 0`.
  Applies to `Gaf02ChainEJA` through its parent `Gaf02ChainE`.
* `gaf02_chainEJA_realization_C14Z_GAFC` (realization wrapper, consumer): the producer
  `gaf02_chainEJA_row_GAFC` on the FINAL family `LocalChartPacketsC14Z` (chain on its
  `LocalChartPacketsC14` projection), with the producer's own `0 < εr`
  (`eventually_nonempty_localChartPacketsC14Z_FAMZ` returns `0 < εr ∧ εr < 1/4 ∧ εr < cap`) in place
  of the row's `0 ≤ εr`; same quantifier order and hypothesis list otherwise; the chain it returns
  satisfies EDP01 with the `C_ρ` fixed before `Δ` and the packet.
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
local instance instMetricNC14_GAFCZ {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAFCZ {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAFCZ {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP01 on the chain on the enhanced planes** (B:6666): the scale `s = C.scale = ℓ_ρ(E)`
satisfies (SD) `|s − ρ| ≤ C_ρΛρ`, `|ds(v)| ≤ C_ρΛ|v|_g` with
`C_ρ = 100(L₀ + 1)(1 + b_cut + 1·c_w(1)/Σ₁) ≥ 100`, `s` is differentiable and `s > 0`. The numeric
inputs `0 ≤ c_w(1)`, `Σ₁ ≤ ε₁/10000` are the ChoiceValidity record's (D66-3). -/
theorem Gaf02ChainE.edp01_GAFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    100 ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) ∧
    ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.scale p ∧
      |C.scale p - ρ p| ≤
        100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * ρ p ∧
      (∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) C.scale p v| ≤
        100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ *
          Real.sqrt (g.inner p v v)) ∧
      0 < C.scale p :=
  C.toChain.edp01_GAF8 (C.rough.cw_nonneg 0) (C.rough.sigma_le 0).le

/-- **Realization wrapper on the final family** (D66-6; consumer of `gaf02_chainEJA_row_GAFC` and
`Gaf02ChainE.edp01_GAFC`): with the ordered quantifiers of `gaf02_chainEJA_row_GAFC`, every packet
`P` of the FINAL family `LocalChartPacketsC14Z` satisfying the verbatim hypothesis list with the
producer's `0 < εr` (instead of the row's explicit `0 ≤ εr`) carries, for every base point `x₀`, a
chain with (JA) on its `LocalChartPacketsC14` projection whose scale satisfies EDP01 with
`C_ρ = 100(L₀ + 1)(1 + b_cut + c_w(1)/Σ₁)`, a constant fixed with `c_w, Σ` before `Δ` and the
packet. -/
theorem gaf02_chainEJA_realization_C14Z_GAFC (Kj : ℕ) {ν cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1)
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
        {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
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
        ζ < 1 / (100 * (1000000 * Δ)) → εr < θs / (100 * (1000000 * Δ)) → 0 < εr →
        ∀ x₀ : X, ∃ C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj
          (fun j => Ξ j (Γ j)) Γ S eg c cw cadj, C.x₀ = x₀ ∧
          100 ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) ∧
          ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.scale p ∧
            |C.scale p - ρ p| ≤
              100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * ρ p ∧
            (∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) C.scale p v| ≤
              100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ *
                Real.sqrt (g.inner p v v)) ∧
            0 < C.scale p := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, hrow⟩ := gaf02_chainEJA_row_GAFC Kj hν hν1 hcadj
  refine ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, fun β₂ hβ₂ hβ₂1 Δ hΔ => ?_⟩
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, hrow'⟩ := hrow β₂ hβ₂ hβ₂1 Δ hΔ
  refine ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
    f27 f28 f29 f30 f31 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5 m6 m7 m8 hεr0 x₀
  obtain ⟨C, hC⟩ := hrow' P.toLocalChartPacketsC14D.toLocalChartPacketsC14 f1 f2 f3 f4 f5 f6 f7 f8
    f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 d1 d2
    d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5 m6 m7 m8 hεr0.le x₀
  exact ⟨C, hC, C.edp01_GAFC⟩

end DifferentialGeometry.Geometry.Collapse
