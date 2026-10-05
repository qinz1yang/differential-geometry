import DifferentialGeometry.Geometry.Fibration.ActualStageChainERow

/-!
# GAF01 as ONE statement: one actual choice for the three adjustments, with the actual clouds

Blueprint `master207B.tex`, GAF01 (`prop:fibration-actual-adjustment-choices`, B:5704–5795):
"For every early target `c_adjust > 0` there is one choice, in the retained order, supplying the
actual hypotheses of CFS31, CFS20 and CGP07 for ALL three stages. One may additionally require (JA)
`Σ_j ≤ ε_j/10000, c₃ < min{c_adjust, 1/1000, 1/512}`. These choices use the actual SGP, EGP and
TCP producers."

The three earlier GAF01 statements were tiers: `gaf01_row` (choice for arbitrary positive graph
moduli), `gaf01_row_nearest_shared_GAFS4` (shared CFS15 modulus, stage maps, choice), and the
chain producers (`gaf02_chain_choice_full_GAF8`: the choice at the ACTUAL graph moduli
`C_TCP, C_EGP, C_SGP` with all its evidence; `gaf02_chainE_row_GAF8`: the actual clouds on the
same choice, but keeping only part of the evidence). `gaf01_full_row_RFC` is the row: ONE call of
`gaf02_chain_choice_full_GAF8` at the early target `min c_adjust (1/1000)` and, on the SAME
numbers, the actual-cloud clause (enhanced planes with FC27's tests, CFS15's native stage outputs,
the rough-graph rows TCP05 / EGP06 / SGP04 at `e_j`, (OS), one-sheet budget and rank margin:
`Gaf02ChainE`). Its conclusion lists

1. per stage: CFS15's modulus `Cfs15ModulusAtV2 k_j K_j (5/3) Ξ_j` at `Γ_j < θ_j`, CFS12's
   interior condition, and (JB): `Σ_j < min{1/2, ε_j/10000, Γ_j/200, Γ_j³/(100C_j)}`,
   `e_j < min{1/100, Γ_jΣ_j/100, Σ_j/1000, 1/(200Ω)}`, `0 ≤ c_w`;
2. the retained order `c₁ ≤ c₂ ≤ c₃` and (JA) `c₃ < min{c_adjust, 1/1000, 1/512}` (the `Σ`-part
   of (JA) is in 1.);
3. per stage, verbatim from the choice: CGP07's (OS) `ε_j < 1/(1000(Ω+1))`, `e_j < Σ_j/1000`,
   `2e_j < 1/(48Ω)`; `ε_j < 1/10`; `ε_j < α_j`; CFS20's three budgets for every `E, H ≤ t_j`,
   `ν ≤ Γ_j`, `σ ≤ 1/2`; CGP06's rank margin `ν + e_j ≤ 1/(48Ω)`; the one-sheet budget (SN);
   `Ω = gafGraphOmega_BAS = max{1, C_TCP, C_EGP, C_SGP}`;
4. CFS31's (MB) order constraints and the kernel numbers (`gaf02_chain_choice_full_GAF8`'s);
5. the actual clouds: the thresholds of the actual producers in their order (first stage; then
   `β₂`; then `Δ ≥ 1200` and the edge / slim thresholds), then on every packet of the final
   family with the producers' hypotheses and every base point `x₀`, a chain
   `Ĉ : Gaf02ChainE` on the SAME numbers with `Ĉ.x₀ = x₀`.

Consumer: `gaf01_full_row_ja_RFC` reads (JA) and (JB) off the row.
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
local instance instMetricNC14_RFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_RFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_RFC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- `e < 1/(200Ω)` from `e < ΓΣ/100`, `Γ < 1`, `Σ < ε/10000` and `ε < 1/(1000(Ω+1))`. -/
theorem rough_lt_omega_RFC {Ω eg Γ S Ξ : ℝ} (hΩ : 1 ≤ Ω) (hΓ1 : Γ < 1) (hS : 0 < S)
    (heΓ : eg < Γ * S / 100) (hSΞ : S < Ξ / 10000) (hΞΩ : Ξ < 1 / (1000 * (Ω + 1))) :
    eg < 1 / (200 * Ω) := by
  have hΩ0 : 0 < Ω := by linarith only [hΩ]
  have hΓS : Γ * S < S := by nlinarith only [hΓ1, hS]
  have hΞ' : Ξ * (1000 * (Ω + 1)) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hΞΩ
    exact hΞΩ
  rw [lt_div_iff₀ (by positivity)]
  have h1 : eg < Ξ / 1000000 := by linarith only [heΓ, hΓS, hSΞ]
  have hΞ0 : 0 < Ξ := by linarith only [hS, hSΞ]
  nlinarith only [h1, hΞ', hΩ0, hΞ0]

/-- **GAF01** (`prop:fibration-actual-adjustment-choices`, B:5704–5795) as ONE statement on ONE
choice. For the jet order `Kj`, the exclusion quality `ν ∈ (0, 1)` and every early target
`c_adj > 0`: the shared CFS15 moduli `θ, Ξ`, one choice `c, Γ, Σ, e` (graph moduli of TCP05,
EGP06, SGP04) and the stage weight constants `c_w` with (1) CFS15 at `Γ_j` and (JB), (2) the
retained order and (JA), (3) CGP07's (OS), CFS20's `α_j`, `t_j` budgets, CGP06's rank margin and
(SN), (4) CFS31's (MB) numbers, and (5) the ACTUAL clouds: after the producers' thresholds, every
packet of the final family with their hypotheses carries, for every `x₀`, a chain on the enhanced
planes on the SAME numbers (rough-graph rows TCP05 / EGP06 / SGP04 at `e_j`, CFS15 outputs). -/
theorem gaf01_full_row_RFC (Kj : ℕ) {ν cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hcadj : 0 < cadj) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ) (c Γ S eg cw : Fin 3 → ℝ),
      (∀ j, 0 < θ j ∧ 0 < Γ j ∧ Γ j < θ j ∧ Γ j < 1 ∧ 0 < Ξ j (Γ j) ∧
        Cfs15ModulusAtV2 (gafStageDim j) Kj (5 / 3) (Ξ j) (Γ j) ∧
        Γ j * ((80 * (5 / 3) + 31) * (Ξ j (Γ j))⁻¹ + 2) < 1 ∧ 0 < S j ∧ S j < 1 / 2 ∧
        S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧ 0 < eg j ∧ eg j < 1 / 100 ∧
        eg j < Γ j * S j / 100 ∧ eg j < S j / 1000 ∧ eg j < 1 / (200 * gafGraphOmega_BAS) ∧
        0 < c j ∧ 0 ≤ cw j) ∧
      S 0 < Γ 0 ^ 3 / (100 * tcpGraphConst) ∧ S 1 < Γ 1 ^ 3 / (100 * egpGraphConst) ∧
      S 2 < Γ 2 ^ 3 / (100 * sgpGraphBound) ∧
      c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧ c 2 < min cadj (min (1 / 1000) (1 / 512)) ∧
      (∀ j, Ξ j (Γ j) < 1 / (1000 * (gafGraphOmega_BAS + 1)) ∧ eg j < S j / 1000 ∧
        2 * eg j < 1 / (48 * gafGraphOmega_BAS) ∧ Ξ j (Γ j) < 1 / 10 ∧
        Ξ j (Γ j) < min (c j / (16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound)))
          (1 / 2 / (8 * (1 + gafDerivativeBound))) ∧
        (∀ E H ν σ : ℝ, 0 ≤ E → E ≤ min (3 * S j / 10) (min (min (c j / (16 * (1 +
            gafCutoffConstant) * (1 + gafDerivativeBound)))
          (1 / 2 / (8 * (1 + gafDerivativeBound)))) 1) → 0 ≤ H →
          H ≤ min (3 * S j / 10) (min (min (c j / (16 * (1 + gafCutoffConstant) * (1 +
              gafDerivativeBound)))
          (1 / 2 / (8 * (1 + gafDerivativeBound)))) 1) → ν ≤ Γ j → σ ≤ 1 / 2 →
          let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
          E + a < c j ∧ a * gafCutoffConstant * (gafDerivativeBound + H) +
              Ξ j (Γ j) * (gafDerivativeBound + H) + ν + 2 * H < c j ∧
            Ξ j (Γ j) * (gafDerivativeBound + H) + H < 1 / 2) ∧
        (∀ ν : ℝ, ν ≤ eg j → ν + eg j ≤ 1 / (48 * gafGraphOmega_BAS)) ∧
        ∀ R rx : ℝ, 0 < R → 9 / 20 * S j * R ≤ rx →
          (2 * eg j + 25 / 12 * (1 + gafGraphOmega_BAS) * Ξ j (Γ j) * S j) * R <
              S j * R / 100 ∧
            S j * R / 100 < rx / 4 ∧ Ξ j (Γ j) < 1 / (2 * gafGraphOmega_BAS)) ∧
      ((∀ j, 0 < Ξ j (Γ j) ∧ 0 < S j ∧ 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 ∧ 0 ≤ eg j) ∧
        5 / 3 * Ξ 0 (Γ 0) * S 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
        (5 / 3 * Ξ 0 (Γ 0) * S 0 * gafCutoffConstant * gafDerivativeBound +
            Ξ 0 (Γ 0) * gafDerivativeBound + eg 0) < c 0 ∧
        c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 3 * S 1 / 10 ∧
        (c 0 + (5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
        ((5 / 3 * Ξ 1 (Γ 1) * S 1 + (1 + Ξ 1 (Γ 1)) * c 0) * gafCutoffConstant *
            (gafDerivativeBound + c 0) +
            Ξ 1 (Γ 1) * (gafDerivativeBound + c 0) + eg 1 + 2 * c 0) < c 1 ∧
        c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 3 * S 2 / 10 ∧
        (c 1 + (5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
        ((5 / 3 * Ξ 2 (Γ 2) * S 2 + (1 + Ξ 2 (Γ 2)) * c 1) * gafCutoffConstant *
            (gafDerivativeBound + c 1) +
            Ξ 2 (Γ 2) * (gafDerivativeBound + c 1) + eg 2 + 2 * c 1) < c 2) ∧
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
        ∀ x₀ : X, ∃ C : Gaf02ChainE P Kj (fun j => Ξ j (Γ j)) Γ S eg c cw, C.x₀ = x₀ := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, hj, hSC₀, hSC₁, hSC₂, hc01, hc12, hc2, hfull, hnum⟩ :=
    gaf02_chain_choice_full_GAF8 Kj (cadj := min cadj (1 / 1000)) (lt_min hcadj (by norm_num))
  obtain ⟨-, hΓ₀, -, hΓ1₀, -, hat₀, hint₀, hS₀, -, hSΓ₀, he₀, he1₀, heΓ₀, -, -⟩ := hj 0
  obtain ⟨-, hΓ₁, -, hΓ1₁, -, hat₁, hint₁, hS₁, -, hSΓ₁, he₁, he1₁, heΓ₁, heS₁, -⟩ := hj 1
  obtain ⟨-, hΓ₂, -, hΓ1₂, -, hat₂, hint₂, hS₂, -, hSΓ₂, he₂, he1₂, heΓ₂, -, -⟩ := hj 2
  obtain ⟨cw₀, hcw₀, hout₀⟩ := gafStage_output_GAF8 0 hΓ₀ hat₀ hint₀
  obtain ⟨cw₁, hcw₁, hout₁⟩ := gafStage_output_GAF8 1 hΓ₁ hat₁ hint₁
  obtain ⟨cw₂, hcw₂, hout₂⟩ := gafStage_output_GAF8 2 hΓ₂ hat₂ hint₂
  have hmo : ∀ j, 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 := fun j => (hnum.1 j).2.2.1
  have hcw : ∀ j, 0 ≤ (![cw₀, cw₁, cw₂] : Fin 3 → ℝ) j := by
    intro j
    fin_cases j
    · exact hcw₀
    · exact hcw₁
    · exact hcw₂
  have hca : c 2 < cadj := hc2.trans_le (min_le_left _ _)
  have hc1000 : c 2 < 1 / 1000 := hc2.trans_le (min_le_right _ _)
  obtain ⟨σP, hσP, hσP1, η₂P, γ₀P, ηcP, θP, hη₂P, hγ₀P, hηcP, hθP, hθP1, hrowP⟩ :=
    exists_firstStagePlanes_PLN hΓ₀ hΓ1₀ hS₀ hSΓ₀ hSC₀ he₀ he1₀ heΓ₀ hν hν1
  obtain ⟨σT, hσT, -, η₂T, γ₀T, ηcT, θT, hη₂T, hγ₀T, hηcT, hθT, -, hrowT⟩ :=
    tcp05_row_out_VAL3 he₀ he1₀ hν hν1
  refine ⟨θ, Ξ, c, Γ, S, eg, ![cw₀, cw₁, cw₂], fun j => ?_, hSC₀, hSC₁, hSC₂, hc01, hc12,
    lt_min hca (lt_min hc1000 (hc1000.trans (by norm_num))), fun j => hfull j, hnum,
    min σP σT, min η₂P η₂T, min (min γ₀P γ₀T) 1, min ηcP ηcT, min θP θT, lt_min hσP hσT,
    (min_le_left _ _).trans hσP1, lt_min hη₂P hη₂T, lt_min (lt_min hγ₀P hγ₀T) one_pos,
    min_le_right _ _, lt_min hηcP hηcT, lt_min hθP hθT, (min_le_left _ _).trans_lt hθP1,
    fun β₂ hβ₂ hβ₂1 Δ hΔ => ?_⟩
  · obtain ⟨hθ, hΓ, hθΓ, hΓ1, hΞ, hat, hint, hS, hSΞ, hSΓ, he, he1, heΓ, heS, hcj⟩ := hj j
    have hΞΩ : Ξ j (Γ j) < 1 / (1000 * (gafGraphOmega_BAS + 1)) := (hfull j).1
    exact ⟨hθ, hΓ, hθΓ, hΓ1, hΞ, hat, hint, hS, by linarith only [hSΓ, hΓ1], hSΞ, hSΓ, he, he1,
      heΓ, heS, rough_lt_omega_RFC one_le_gafGraphOmega_BAS hΓ1 hS heΓ hSΞ hΞΩ, hcj, hcw j⟩
  obtain ⟨η₁P, hη₁P, hrowP'⟩ := hrowP Δ hΔ
  obtain ⟨η₁T, hη₁T, hrowT'⟩ := hrowT Δ hΔ
  have hΔ1 : 1 ≤ Δ := by linarith only [hΔ]
  obtain ⟨LcE, η₀E, hLcE, hη₀E, hrowE⟩ := exists_edgeStagePlanes_PLN (Γ := Γ 1) (Sg := S 1)
    (eg := eg 1) hΔ1 hβ₂ hβ₂1 ⟨hΓ₁, hΓ1₁⟩ hS₁ (lt_min hSΓ₁ hSC₁) he₁
    (lt_min he1₁ (lt_min heΓ₁ heS₁))
  obtain ⟨LcG, η₀G, -, hη₀G, hrowG⟩ := egp06_row_out_VAL3 (eg := eg 1) hΔ1 hβ₂ hβ₂1 he₁ he1₁
  obtain ⟨θS, hθS, hθS1, LcS, η₀S, hLcS, hη₀S, hrowS⟩ :=
    exists_slimStagePlanes_PLN hΔ1 hβ₂ (by linarith only [hβ₂1]) hΓ₂ hΓ1₂ hS₂ hSΓ₂ hSC₂ he₂ he1₂
      heΓ₂
  obtain ⟨θR, hθR, -, LcR, η₀R, -, hη₀R, hrowR⟩ :=
    sgp04_row_out_VAL3 (eg := eg 2) hΔ1 hβ₂ (by linarith only [hβ₂1]) he₂ he1₂
  refine ⟨min η₁P η₁T, max LcE LcG, min η₀E η₀G, min θS θR, max LcS LcR, min η₀S η₀R,
    lt_min hη₁P hη₁T, lt_max_of_lt_left hLcE, lt_min hη₀E hη₀G, lt_min hθS hθR,
    (min_le_left _ _).trans_lt hθS1, lt_max_of_lt_left hLcS, lt_min hη₀S hη₀R, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
    f27 f28 f29 f30 f31 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 m1 m2 m3 m4 m5 m6 m7 m8 hεr0 x₀
  have hθm : 0 < min θP θT := lt_min hθP hθT
  have hθP2 : min θP θT ^ 2 ≤ θP ^ 2 := pow_le_pow_left₀ hθm.le (min_le_left _ _) 2
  have hθT2 : min θP θT ^ 2 ≤ θT ^ 2 := pow_le_pow_left₀ hθm.le (min_le_right _ _) 2
  have hθs : 0 < min θS θR := lt_min hθS hθR
  have hθS2 : min θS θR ^ 2 ≤ θS ^ 2 := pow_le_pow_left₀ hθs.le (min_le_left _ _) 2
  have hθR2 : min θS θR ^ 2 ≤ θR ^ 2 := pow_le_pow_left₀ hθs.le (min_le_right _ _) 2
  have hσPi : σP⁻¹ ≤ (min σP σT)⁻¹ := inv_anti₀ (lt_min hσP hσT) (min_le_left _ _)
  have hσTi : σT⁻¹ ≤ (min σP σT)⁻¹ := inv_anti₀ (lt_min hσP hσT) (min_le_right _ _)
  have hD : (0 : ℝ) ≤ 100 * (1000000 * Δ) := by linarith only [hΔ1]
  have hθPl := min_le_left θP θT
  have hθTl := min_le_right θP θT
  have hθSl := min_le_left θS θR
  have hθRl := min_le_right θS θR
  obtain ⟨A₀⟩ := hrowP' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (by linarith only [f11, hθP2])
    (by linarith only [f12, hθPl]) f13 f14 (f15.trans (min_le_left _ _))
    (f16.trans (min_le_left _ _))
    (f17.trans ((min_le_left _ _).trans (min_le_left _ _))) f18
    (f19.trans ((min_le_left _ _).trans (min_le_left _ _))) (f20.trans (min_le_left _ _))
    (f21.trans (min_le_left _ _)) (f22.trans (min_le_left _ _)) f23 (by linarith only [f24, hθP2])
    (by linarith only [f25, hθPl]) f26 (by linarith only [f27, hθP2])
    (by linarith only [f28, hθPl]) f29 (hσPi.trans f30) f31
  have hT05 := hrowT' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 (by linarith only [f11, hθT2])
    (by linarith only [f12, hθTl]) f13 f14 (f15.trans (min_le_right _ _))
    (f16.trans (min_le_right _ _))
    (f17.trans ((min_le_left _ _).trans (min_le_right _ _))) f18
    (f19.trans ((min_le_left _ _).trans (min_le_right _ _))) (f20.trans (min_le_right _ _))
    (f21.trans (min_le_right _ _)) (f22.trans (min_le_right _ _)) f23
    (by linarith only [f24, hθT2]) (by linarith only [f25, hθTl]) f26
    (by linarith only [f27, hθT2]) (by linarith only [f28, hθTl]) f29 (hσTi.trans f30) f31
  obtain ⟨A₁⟩ := hrowE X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      P (d1.trans (min_le_left _ _)) d2 (d3.trans (min_le_left _ _)) ((le_max_left _ _).trans d4)
      f1 f4 f2 f3 d5 d6 f23 d7 d8 f6 f7 f29 f26 d9 d10 d11
  have hE06 := hrowG X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P.toLocalChartPacketsRVZ (d1.trans (min_le_right _ _)) d2 (d3.trans (min_le_right _ _))
    ((le_max_right _ _).trans d4) f1 f4 f2 f3 d5 d6 f23 d7 d8 f6 f7 f29 f26 d9 d10 d11
  obtain ⟨A₂⟩ := hrowS X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      P m1 (m2.trans (min_le_left _ _)) ((le_max_left _ _).trans m3) f1 f4 f6 f7 f29 f23
      (by linarith only [m4, hθS2]) (by linarith only [m5, hθSl]) f26
      (by linarith only [m6, hθS2]) m7 (m8.trans_le (div_le_div_of_nonneg_right hθSl hD))
  have hS04 := hrowR X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P.toLocalChartPacketsRVZ m1 (m2.trans (min_le_right _ _)) ((le_max_right _ _).trans m3) f1 f4
    f6 f7 f29 f23 (by linarith only [m4, hθR2]) (by linarith only [m5, hθRl]) f26
    (by linarith only [m6, hθR2]) m7 (m8.trans_le (div_le_div_of_nonneg_right hθRl hD))
  have he8 : e ≤ 1 / 8 := by linarith only [f6]
  have O₀ := (hout₀ P f1 hΔ1 f2 f3 he8 f4 (A₀.rsel x₀) (A₀.cfs15_inputs x₀).1 (S 0) hS₀
    (hmo 0) A₀.plane (fun x hx => (A₀.dimension x hx).1)
    (A₀.cloudy (A₀.rsel x₀) (A₀.cfs15_inputs x₀).1)).some
  have O₁ := (hout₁ P f1 hΔ1 f2 f3 he8 f4 (A₁.rsel x₀) (A₁.cfs15_inputs x₀).1 (S 1) hS₁
    (hmo 1) A₁.plane (fun x hx => (A₁.dimension x hx).1)
    (A₁.cloudy (A₁.rsel x₀) (A₁.cfs15_inputs x₀).1)).some
  have O₂ := (hout₂ P f1 hΔ1 f2 f3 he8 f4 (A₂.rsel x₀) (A₂.cfs15_inputs x₀).1 (S 2) hS₂
    (hmo 2) A₂.plane (fun x hx => (A₂.dimension x hx).1)
    (A₂.cloudy (A₂.rsel x₀) (A₂.cfs15_inputs x₀).1)).some
  have hθt2 : min θP θT ^ 2 < 1 := by
    nlinarith only [mul_lt_mul_of_pos_left ((min_le_left θP θT).trans_lt hθP1) hθm,
      (min_le_left θP θT).trans_lt hθP1]
  exact gaf02_chainE_mk_GAF8 P ⟨f1, hΔ1, f2, f3, f4, f5, f6, f7, f23.le,
    by linarith only [f24, hθt2], ⟨f10, by linarith only [f11, hθt2]⟩,
    ⟨f18.le, f19.trans (min_le_right _ _)⟩, ⟨hεr0, by linarith only [f28, hθPl, hθP1]⟩⟩ hnum x₀
    A₀ A₁ A₂ O₀ O₁ O₂ hT05 hE06 hS04
    (fun j => ⟨(hfull j).1, (hfull j).2.1, (hfull j).2.2.1⟩) (fun j => (hfull j).2.2.2.2.2.2.2)
    (fun j => (hfull j).2.2.2.2.2.2.1) (fun j => (hj j).2.2.2.2.2.2.2.2.1) hcw

end DifferentialGeometry.Geometry.Collapse
