import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJARow

/-!
# The enhanced assembler as a definition, its projections, and a realizable producer

Review 71, dispositions D71-1, D71-5, D71-9, D71-10 (`docs/geometrization/chapter14/out/
dispositions-task71-chainE-bases-as-built.md`).

* D71-1: `gaf02_chainE_mk_GAF8` only states `∃ CE, CE.x₀ = x₀`. Here the SAME assembly is a
  definition, `Gaf02ChainE.ofOutputs_GAFC` (enhanced planes `A_j`, native outputs `O_j` with plane
  slot `A_j.plane`, rough facts), with its projection theorem `Gaf02ChainE.ofOutputs_data_GAFC` in
  the
  style of `Gaf02Chain.ofOutputs_data`: `toChain = Gaf02Chain.ofOutputs …`,
  `toChain.slot j = .active O_j`,
  `toChain.sel = ![A₀.rsel x₀, A₁.rsel x₀, A₂.rsel x₀]`,
  `toChain.plane = ![A₀.plane, A₁.plane, A₂.plane]`,
  the slot maps are the outputs' ambient maps, and the plane witnesses / base point are the given
  ones (all `rfl`). A register that passes its own outputs reuses this without unfolding an
  existence proof. `Gaf02ChainEJA.ofOutputs_GAFC` adds the `c₃`-part of (JA).
* D71-5: the rows take `0 < ν < 1` but then require `3ν ≤ β 3 < 1`, so for `1/3 ≤ ν` they are
  vacuous. `gaf02_chainEJA_row_beta3_GAFC` PROMISES realizability on the `β₃` side: it takes the
  value `β₃` with `0 < β₃ ≤ threeSplittingExclusionThreshold` (the final family producer's range for
  `β 3`), puts `ν = β₃/3`, and asks `β 3 = β₃` of the packet instead of `3ν ≤ β 3 < 1` (same
  quantifier order and hypothesis list otherwise). The general rows stay.
* D71-9 / D71-10: the default entries are `gaf02_chain_row_reordered_CHI`, `gaf02_chainE_row_GAF8`
  and `gaf02_chainEJA_row_GAFC` (old `gaf02_chain_row_GAF8` retired as default); (JA) is the
  `c₃`-part only — the full (JB) / (SE) budgets are NOT stored in `Gaf02ChainEJA`.
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
local instance instMetricNC14_GAFCA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAFCA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAFCA {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The enhanced assembler as a definition** (D66-2, D71-1): on given enhanced plane witnesses
`A_j`, native outputs `O_j` whose plane slot is `A_j.plane` and radius `Σ_jρ ∘ A_j.rsel x₀`, the
packet hypotheses, the numbers and the rough facts, the chain on the enhanced planes whose
`toChain` is `Gaf02Chain.ofOutputs …` (the term of `gaf02_chainE_mk_GAF8`). -/
def Gaf02ChainE.ofOutputs_GAFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (hstd : 0 ≤ Λ ∧ 1 ≤ Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    0 ≤ σs ∧ σs ≤ 1 / 100 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1)
    (hnum : (∀ j, 0 < Ξ j ∧ 0 < S j ∧ 128 * (Ξ j)⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2)
    (x₀ : X) (A₀ : FirstStagePlanes_PLN P (Γ 0) (S 0) (eg 0))
    (A₁ : EdgeStagePlanes_PLN P (Γ 1) (S 1) (eg 1)) (A₂ : SlimStagePlanes_PLN P (Γ 2) (S 2) (eg 2))
    (O₀ : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0) (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) (fun x => S 0 * ρ (A₀.rsel x₀ x)) A₀.plane)
    (O₁ : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (A₁.rsel x₀ x)) A₁.plane)
    (O₂ : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (A₂.rsel x₀ x)) A₂.plane)
    (hT05 : Tcp05OutV2 P (eg 0)) (hE06 : Egp06OutV2 P.toLocalChartPacketsRVZ (eg 1))
    (hS04 : Sgp04OutV2 P.toLocalChartPacketsRVZ (eg 2))
    (hos : ∀ j, Ξ j < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧ eg j < S j / 1000 ∧
      2 * eg j < 1 / (48 * gafGraphOmega_BAS))
    (hone : ∀ j (Rr rx : ℝ), 0 < Rr → 9 / 20 * S j * Rr ≤ rx →
      (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j * S j) * Rr < S j * Rr / 100 ∧
        S j * Rr / 100 < rx / 4 ∧ Ξ j < 1 / (2 * gafGraphOmega_BAS))
    (hrank : ∀ j (ν : ℝ), ν ≤ eg j → ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS))
    (hsig : ∀ j, S j < Ξ j / 10000) (hcw : ∀ j, 0 ≤ cw j)
    : Gaf02ChainE P Kj Ξ Γ S eg c cw := by
  have hsel : ∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        ((![A₀.rsel x₀, A₁.rsel x₀, A₂.rsel x₀] : Fin 3 → BlockSpace (fun _ : CGPTag
            P.toLocalChartFamily P.zero => ℝ²) → X) st x) = x := by
    intro st
    fin_cases st
    · exact (A₀.cfs15_inputs x₀).1
    · exact (A₁.cfs15_inputs x₀).1
    · exact (A₂.cfs15_inputs x₀).1
  exact {
    toChain := Gaf02Chain.ofOutputs hstd hnum ![A₀.rsel x₀, A₁.rsel x₀, A₂.rsel x₀] hsel
      ![A₀.plane, A₁.plane, A₂.plane] (gaf02_test0_of_planes_GAF8 A₀) (gaf02_test1_of_planes_GAF8
          A₁)
      (gaf02_test2_of_planes_GAF8 A₂) fun st => match st with
        | ⟨0, _⟩ => O₀
        | ⟨1, _⟩ => O₁
        | ⟨2, _⟩ => O₂
        | ⟨k + 3, hk⟩ => absurd hk (by omega)
    x₀ := x₀
    planes₀ := A₀
    planes₁ := A₁
    planes₂ := A₂
    sel_eq := ⟨rfl, rfl, rfl⟩
    plane_eq := ⟨rfl, rfl, rfl⟩
    rough := ⟨hT05, hE06, hS04, hos, hone, hrank, hsig, hcw⟩ }

/-- **Projections of the enhanced assembler** (D71-1, in the style of `Gaf02Chain.ofOutputs_data`):
the base point and plane witnesses are the given ones; the chain's selections and planes are the
witnesses' `rsel x₀` and `plane`; every slot is `.active` with the given output, whose ambient
nearest map is the slot map. -/
theorem Gaf02ChainE.ofOutputs_data_GAFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (hstd : 0 ≤ Λ ∧ 1 ≤ Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    0 ≤ σs ∧ σs ≤ 1 / 100 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1)
    (hnum : (∀ j, 0 < Ξ j ∧ 0 < S j ∧ 128 * (Ξ j)⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2)
    (x₀ : X) (A₀ : FirstStagePlanes_PLN P (Γ 0) (S 0) (eg 0))
    (A₁ : EdgeStagePlanes_PLN P (Γ 1) (S 1) (eg 1)) (A₂ : SlimStagePlanes_PLN P (Γ 2) (S 2) (eg 2))
    (O₀ : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0) (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) (fun x => S 0 * ρ (A₀.rsel x₀ x)) A₀.plane)
    (O₁ : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (A₁.rsel x₀ x)) A₁.plane)
    (O₂ : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (A₂.rsel x₀ x)) A₂.plane)
    (hT05 : Tcp05OutV2 P (eg 0)) (hE06 : Egp06OutV2 P.toLocalChartPacketsRVZ (eg 1))
    (hS04 : Sgp04OutV2 P.toLocalChartPacketsRVZ (eg 2))
    (hos : ∀ j, Ξ j < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧ eg j < S j / 1000 ∧
      2 * eg j < 1 / (48 * gafGraphOmega_BAS))
    (hone : ∀ j (Rr rx : ℝ), 0 < Rr → 9 / 20 * S j * Rr ≤ rx →
      (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j * S j) * Rr < S j * Rr / 100 ∧
        S j * Rr / 100 < rx / 4 ∧ Ξ j < 1 / (2 * gafGraphOmega_BAS))
    (hrank : ∀ j (ν : ℝ), ν ≤ eg j → ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS))
    (hsig : ∀ j, S j < Ξ j / 10000) (hcw : ∀ j, 0 ≤ cw j)
    :
    (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank hsig
        hcw).x₀ = x₀ ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).planes₀ = A₀ ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).planes₁ = A₁ ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).planes₂ = A₂ ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.sel = ![A₀.rsel x₀, A₁.rsel x₀, A₂.rsel x₀] ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.plane = ![A₀.plane, A₁.plane, A₂.plane] ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.slot 0 = .active O₀ ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.slot 1 = .active O₁ ∧
      (Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.slot 2 = .active O₂ ∧
      ((Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.slot 0).map = O₀.ambient ∧
      ((Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.slot 1).map = O₁.ambient ∧
      ((Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw).toChain.slot 2).map = O₂.ambient :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The enhanced assembler with (JA)**: `Gaf02ChainE.ofOutputs_GAFC` together with the
`c₃`-part of (JA) for the early target `cadj`. -/
def Gaf02ChainEJA.ofOutputs_GAFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (hstd : 0 ≤ Λ ∧ 1 ≤ Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    0 ≤ σs ∧ σs ≤ 1 / 100 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1)
    (hnum : (∀ j, 0 < Ξ j ∧ 0 < S j ∧ 128 * (Ξ j)⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2)
    (x₀ : X) (A₀ : FirstStagePlanes_PLN P (Γ 0) (S 0) (eg 0))
    (A₁ : EdgeStagePlanes_PLN P (Γ 1) (S 1) (eg 1)) (A₂ : SlimStagePlanes_PLN P (Γ 2) (S 2) (eg 2))
    (O₀ : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0) (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) (fun x => S 0 * ρ (A₀.rsel x₀ x)) A₀.plane)
    (O₁ : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (A₁.rsel x₀ x)) A₁.plane)
    (O₂ : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (A₂.rsel x₀ x)) A₂.plane)
    (hT05 : Tcp05OutV2 P (eg 0)) (hE06 : Egp06OutV2 P.toLocalChartPacketsRVZ (eg 1))
    (hS04 : Sgp04OutV2 P.toLocalChartPacketsRVZ (eg 2))
    (hos : ∀ j, Ξ j < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧ eg j < S j / 1000 ∧
      2 * eg j < 1 / (48 * gafGraphOmega_BAS))
    (hone : ∀ j (Rr rx : ℝ), 0 < Rr → 9 / 20 * S j * Rr ≤ rx →
      (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j * S j) * Rr < S j * Rr / 100 ∧
        S j * Rr / 100 < rx / 4 ∧ Ξ j < 1 / (2 * gafGraphOmega_BAS))
    (hrank : ∀ j (ν : ℝ), ν ≤ eg j → ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS))
    (hsig : ∀ j, S j < Ξ j / 10000) (hcw : ∀ j, 0 ≤ cw j) {cadj : ℝ}
    (hca : c 2 < cadj) (h1000 : c 2 < 1 / 1000)
    : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj :=
  { Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank hsig
      hcw with c_lt_adj := hca, c_two_lt := h1000 }

/-- The (JA) assembler's underlying chain on the enhanced planes is `Gaf02ChainE.ofOutputs_GAFC`. -/
theorem Gaf02ChainEJA.ofOutputs_toGaf02ChainE_GAFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (hstd : 0 ≤ Λ ∧ 1 ≤ Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    0 ≤ σs ∧ σs ≤ 1 / 100 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1)
    (hnum : (∀ j, 0 < Ξ j ∧ 0 < S j ∧ 128 * (Ξ j)⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
    5 / 3 * Ξ 0 * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
    (5 / 3 * Ξ 0 * S 0 * gafCutoffConstant * gafDerivativeBound +
        Ξ 0 * gafDerivativeBound + eg 0) < c 0 ∧
    c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
    (c 0 + (5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 1 * S 1 + (1 + Ξ 1) * c 0) * gafCutoffConstant * (gafDerivativeBound + c 0) +
        Ξ 1 * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
    c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
    (c 1 + (5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
    ((5 / 3 * Ξ 2 * S 2 + (1 + Ξ 2) * c 1) * gafCutoffConstant * (gafDerivativeBound + c 1) +
        Ξ 2 * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2)
    (x₀ : X) (A₀ : FirstStagePlanes_PLN P (Γ 0) (S 0) (eg 0))
    (A₁ : EdgeStagePlanes_PLN P (Γ 1) (S 1) (eg 1)) (A₂ : SlimStagePlanes_PLN P (Γ 2) (S 2) (eg 2))
    (O₀ : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0) (gafCloud P.toLocalChartFamily P.zero 0)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 0) (fun x => S 0 * ρ (A₀.rsel x₀ x)) A₀.plane)
    (O₁ : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1) (gafCloud P.toLocalChartFamily P.zero 1)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 1) (fun x => S 1 * ρ (A₁.rsel x₀ x)) A₁.plane)
    (O₂ : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2) (gafCloud P.toLocalChartFamily P.zero 2)
      (gafCloudEnlarged P.toLocalChartFamily P.zero 2) (fun x => S 2 * ρ (A₂.rsel x₀ x)) A₂.plane)
    (hT05 : Tcp05OutV2 P (eg 0)) (hE06 : Egp06OutV2 P.toLocalChartPacketsRVZ (eg 1))
    (hS04 : Sgp04OutV2 P.toLocalChartPacketsRVZ (eg 2))
    (hos : ∀ j, Ξ j < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧ eg j < S j / 1000 ∧
      2 * eg j < 1 / (48 * gafGraphOmega_BAS))
    (hone : ∀ j (Rr rx : ℝ), 0 < Rr → 9 / 20 * S j * Rr ≤ rx →
      (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j * S j) * Rr < S j * Rr / 100 ∧
        S j * Rr / 100 < rx / 4 ∧ Ξ j < 1 / (2 * gafGraphOmega_BAS))
    (hrank : ∀ j (ν : ℝ), ν ≤ eg j → ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS))
    (hsig : ∀ j, S j < Ξ j / 10000) (hcw : ∀ j, 0 ≤ cw j) {cadj : ℝ}
    (hca : c 2 < cadj) (h1000 : c 2 < 1 / 1000)
    :
    (Gaf02ChainEJA.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
        hsig hcw hca h1000).toGaf02ChainE =
      Gaf02ChainE.ofOutputs_GAFC P hstd hnum x₀ A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04 hos hone hrank
          hsig hcw :=
  rfl

/-- **A realizable entry of the producer on the `β₃` side** (D71-5): for every `β₃` in the final
family producer's range `0 < β₃ ≤ threeSplittingExclusionThreshold`, the statement of
`gaf02_chainEJA_row_GAFC` at `ν = β₃/3` with the packet premise `β 3 = β₃` (instead of
`3ν ≤ β 3 < 1`, vacuous for `ν ≥ 1/3`); every other quantifier and premise verbatim. -/
theorem gaf02_chainEJA_row_beta3_GAFC (Kj : ℕ) {β₃ cadj : ℝ} (hβ₃ : 0 < β₃)
    (hβ₃T : β₃ ≤ threeSplittingExclusionThreshold.{0, 0}) (hcadj : 0 < cadj) :
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
        0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 → β 3 = β₃ →
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
  have hT := threeSplittingExclusionThreshold_lt.{0, 0}
  have hβ₃1 : β₃ < 1 := hβ₃T.trans_lt (hT.trans (by norm_num))
  obtain ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, hrow⟩ := gaf02_chainEJA_row_GAFC Kj (ν := β₃ / 3) (by positivity)
      (by linarith) hcadj
  refine ⟨θ, Ξ, c, Γ, S, eg, cw, hj, hc01, hc12, hc2, σ, η₂, γ₀, ηc, θt, hσ, hσ1, hη₂, hγ₀, hγ₀1,
    hηc, hθt, hθt1, fun β₂ hβ₂ hβ₂1 Δ hΔ => ?_⟩
  obtain ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, hrow'⟩ := hrow β₂ hβ₂ hβ₂1 Δ hΔ
  refine ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, k1, k2, k3, k4, k5, k6, k7, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 hb3 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
    f27 f28 f29 f30 f31 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5 m6 m7 m8 hεr0 x₀
  have h13 : 3 * (β₃ / 3) ≤ β 3 := by rw [hb3]; linarith
  have h14 : β 3 < 1 := by rw [hb3]; exact hβ₃1
  exact hrow' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 h13 h14 f15 f16 f17 f18 f19 f20 f21 f22 f23
    f24 f25 f26 f27 f28 f29 f30 f31 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5 m6 m7 m8 hεr0
    x₀

end DifferentialGeometry.Geometry.Collapse
