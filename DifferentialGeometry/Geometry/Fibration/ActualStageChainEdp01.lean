import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow
import DifferentialGeometry.Geometry.Fibration.ActualAdjustedScaleStageOneApplications

/-!
# EDP01 on the chain object: the actual adjusted scale `s = ℓ_ρ(E)` varies slowly

Blueprint `master207B.tex`, EDP01 (B:6666–6735); draft 59 §3.4 (EDP01 is proved on the SAME `s` as
GAF02 CORE's scale exit). For a chain `C` on the final family, `s = C.scale = ℓ_ρ(E) = ℓ_ρ(g₁)` is
the first-stage blend `(1 − χ)ρ + χ z_ρ` (`Gaf02Chain.scale_eq_first_blend`), `z_ρ = ℓ_ρ(a₀ ∘ 𝓔⁰)`
with `a₀` the stage-one slot's own nearest map; `edp01_stage_one_blend_step_GAFS2` (with the slot's
differentiability and (SMV), the first test's scale clause) gives (SD) with
`C_ρ = 100(L₀ + 1)(1 + b_cut + N_b c_w/Σ₁)`, `N_b = 1` (CFS11's count is absorbed into the total
weight
budget `c_w`), an early constant (it depends only on `c_w`, `Σ₁`).

* `Gaf02Chain.edp01_GAF8`: (SD) and `C_ρ ≥ 100` for any chain with `0 ≤ c_w(1)`, `Σ₁ ≤ Ξ₁/10⁴`;
  `s > 0` everywhere (GAF02 CORE's coarse error, no condition on `C_ρΛ`).
* `gaf02_edp01_row_GAF8` (consumer): EDP01 on the final family, with the ordered quantifiers of
  `gaf02_chain_row_GAF8` (`C_ρ` is fixed with `c_w, Σ` BEFORE `Δ` and the packet).
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
local instance instMetricNC14_GAF8e {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF8e {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF8e {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP01 on the chain object** (B:6666): for a chain `C` on the final family with `0 ≤ c_w(1)`
and
`Σ₁ ≤ Ξ₁/10⁴`, the scale `s = C.scale = ℓ_ρ(E)` satisfies (SD) `|s − ρ| ≤ C_ρΛρ`,
`|ds(v)| ≤ C_ρΛ|v|_g`
with `C_ρ = 100(L₀ + 1)(1 + b_cut + 1·c_w/Σ₁) ≥ 100`, `s` is differentiable, and `s > 0`. -/
theorem Gaf02Chain.edp01_GAF8 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) :
    100 ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) ∧
    ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.scale p ∧
      |C.scale p - ρ p| ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0)
          * Λ * ρ p ∧
      (∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) C.scale p v| ≤
        100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ *
          Real.sqrt (g.inner p v v)) ∧
      0 < C.scale p := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hLΛ, hLmax, he, hT, hσs, hσs1, hσc, hγc, hεr⟩ := C.std
  obtain ⟨hnum, -⟩ := C.numbers
  have hS0 : 0 < S 0 := (hnum 0).2.1
  have key := edp01_stage_one_blend_step_GAFS2 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc hγc hεr
    (hnum 0).1 hS0 hSΞ hcw (C.sel 0) (C.hsel 0) (C.plane 0) C.test0.2.2.2.1 (C.slot 0).map
    (fun x hx z hz => ((C.slot 0).bounds x hx z hz).2.1) (C.slot 0).mean
  have hfun : C.scale = fun y =>
      (1 - markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
        (cgpGlobalMap P.toLocalChartFamily P.zero y)) * ρ y +
      markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
        (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
        (cgpGlobalMap P.toLocalChartFamily P.zero y) *
      blockMarkerCLM (cgpScaleTag P.toLocalChartFamily P.zero) ((C.slot 0).map (cgpGlobalMap
          P.toLocalChartFamily P.zero y)) :=
    funext fun y => (C.scale_eq_first_blend y).2
  have hC1 : 1 ≤ gafDerivativeBound + 1 := by linarith only [one_le_gafDerivativeBound]
  have hC2 : 1 ≤ 1 + gafCutoffConstant + 1 * cw 0 / S 0 := by
    have h' : 0 ≤ 1 * cw 0 / S 0 := div_nonneg (by linarith only [hcw]) hS0.le
    linarith only [h', gafCutoffConstant_nonneg]
  have hprod := mul_le_mul hC1 hC2 zero_le_one (by linarith only [hC1])
  refine ⟨by nlinarith only [hprod], fun p => ⟨?_, ?_, fun v => ?_, (C.scale_pos p).2⟩⟩
  · rw [hfun]
    exact (key p).1
  · rw [hfun]
    exact (key p).2.1
  · rw [hfun]
    exact (key p).2.2.1 v

/-- **EDP01 on the final family** (consumer of `gaf02_chain_row_GAF8` and `Gaf02Chain.edp01_GAF8`):
with
the ordered quantifiers of `gaf02_chain_row_GAF8` (GAF01 moduli, CHOICE and the weight constants
`c_w` first, so `C_ρ = 100(L₀ + 1)(1 + b_cut + c_w(1)/Σ₁)` is fixed BEFORE `Δ` and the packet),
every
packet of the final family with the tests' hypotheses and every selection carry a chain `C` whose
scale `s = ℓ_ρ(E)` satisfies EDP01's (SD) with this `C_ρ ≥ 100` and `s > 0`. -/
theorem gaf02_edp01_row_GAF8 (Kj : ℕ) {ν β₂ cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1 / 1000000) (hcadj : 0 < cadj) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ) (c Γ S eg cw : Fin 3 → ℝ),
      (∀ j, 0 < θ j ∧ 0 < Γ j ∧ Γ j < θ j ∧ 0 < Ξ j (Γ j) ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξ j) (Γ j) ∧ 0 < S j ∧
        S j < Ξ j (Γ j) / 10000 ∧ 0 < eg j ∧ eg j < Γ j * S j / 100 ∧ 0 < c j ∧ 0 ≤ cw j) ∧
      c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧ c 2 < cadj ∧
      ∃ σ η₂ γ₀ ηc θt : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ 0 < η₂ ∧ 0 < γ₀ ∧ γ₀ ≤ 1 ∧ 0 < ηc ∧
        0 < θt ∧ θt < 1 ∧
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
        ∀ sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) (sel
              st x) = x) →
        ∃ C : Gaf02Chain P.toLocalChartPackets Kj (fun j => Ξ j (Γ j)) Γ S eg c cw,
          C.sel = sel ∧
          100 ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) ∧
          ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.scale p ∧
            |C.scale p - ρ p| ≤ 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0
                / S 0) * Λ * ρ p ∧
            (∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) C.scale p v| ≤
              100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ *
                Real.sqrt (g.inner p v v)) ∧
            0 < C.scale p := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, hrow⟩ := gaf02_chain_row_GAF8 Kj hν hν1 hβ₂ hβ₂1 hcadj
  refine ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, hrow'⟩ := hrow Δ hΔ
  refine ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
        f27 f28 f29 f30 f31
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
    m1 m2 m3 m4 m5 m6 m7 m8 hεr0 sel hsel
  obtain ⟨C, hC⟩ := hrow' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
    f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
    m1 m2 m3 m4 m5 m6 m7 m8 hεr0 sel hsel
  obtain ⟨-, -, -, -, -, -, hSΞ, -, -, -, hcw⟩ := hj 0
  exact ⟨C, hC, C.edp01_GAF8 hcw hSΞ.le⟩

end DifferentialGeometry.Geometry.Collapse
