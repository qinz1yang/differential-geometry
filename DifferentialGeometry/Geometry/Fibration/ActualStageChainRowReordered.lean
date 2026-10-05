import DifferentialGeometry.Geometry.Fibration.ActualStageChainRow

/-!
# GAF02 CORE: the reordered producer of the chain object (lane C14-CHAIN-INST, G2)

`gaf02_chain_row_GAF8` (`ActualStageChainRow.lean`) states its ordered quantifiers with
`β₂` before FC27's first-test thresholds `σ, η₂`, but its packet premises contain `3 * β 2 ≤ σ`,
`β 2 ≤ η₂` and `β 2 = β₂`. A consumer must choose `β₂` before it sees `σ, η₂`, so from the statement
alone the premises are not known to be satisfiable together.

* `gaf02_chain_row_reordered_CHI`: the same producer with `β₂` quantified after
  `σ, η₂, γ₀, ηc, θt` (and before `Δ`). The proof is the original one; the first test does not use
  `β₂`.
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

/-- **GAF02 CORE producer with the thresholds BEFORE `β₂`** (lane C14-CHAIN-INST; the statement of
`gaf02_chain_row_GAF8` with one binder moved). In `gaf02_chain_row_GAF8` the edge/slim quality `β₂` is
fixed before FC27's first-test thresholds `σ, η₂`, while the packet premises require `3β₂ ≤ σ` and
`β₂ ≤ η₂`; from that statement alone no `β₂` is guaranteed to meet them. Here `σ, η₂, γ₀, ηc, θt`
(and GAF01's numbers, the weight constants) come first, then every `β₂ ∈ (0, 10⁻⁶)`, then every
`Δ ≥ 1200`; the premises are verbatim. The proof is `gaf02_chain_row_GAF8`'s: the first test
`fc27_first_test_pps_GAF5` does not use `β₂`; only the edge and slim tests do. -/
theorem gaf02_chain_row_reordered_CHI (Kj : ℕ) {ν cadj : ℝ} (hν : 0 < ν) (hν1 : ν < 1)
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
        ∀ sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) (sel
              st x) = x) →
        ∃ C : Gaf02Chain P.toLocalChartPackets Kj (fun j => Ξ j (Γ j)) Γ S eg c cw,
          C.sel = sel := by
  obtain ⟨θ, Ξ, c, Γ, S, eg, hj, hSC₀, hSC₁, hSC₂, hc01, hc12, hc2, hnum⟩ :=
    gaf02_chain_choice_GAF8 Kj hcadj
  obtain ⟨-, hΓ₀, -, hΓ1₀, -, hat₀, hint₀, hS₀, -, hSΓ₀, he₀, he1₀, heΓ₀, -, -⟩ := hj 0
  obtain ⟨-, hΓ₁, -, hΓ1₁, -, hat₁, hint₁, hS₁, -, hSΓ₁, he₁, he1₁, heΓ₁, heS₁, -⟩ := hj 1
  obtain ⟨-, hΓ₂, -, hΓ1₂, -, hat₂, hint₂, hS₂, -, hSΓ₂, he₂, he1₂, heΓ₂, -, -⟩ := hj 2
  obtain ⟨cw₀, hcw₀, hout₀⟩ := gafStage_output_GAF8 0 hΓ₀ hat₀ hint₀
  obtain ⟨cw₁, hcw₁, hout₁⟩ := gafStage_output_GAF8 1 hΓ₁ hat₁ hint₁
  obtain ⟨cw₂, hcw₂, hout₂⟩ := gafStage_output_GAF8 2 hΓ₂ hat₂ hint₂
  have hmo : ∀ j, 128 * (Ξ j (Γ j))⁻¹ * S j ≤ 1 / 5 := fun j => (hnum.1 j).2.2.1
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hrow1⟩ :=
    fc27_first_test_pps_GAF5 hΓ₀ hΓ1₀ hS₀ hSΓ₀ hSC₀ he₀ he1₀ heΓ₀ hν hν1
  refine ⟨θ, Ξ, c, Γ, S, eg, ![cw₀, cw₁, cw₂], fun j => ?_, hc01, hc12, hc2, σ, η₂, min γ₀ 1, ηc,
    θt, hσ, hσ1, hη₂, lt_min hγ₀ one_pos, min_le_right _ _, hηc, hθt, hθt1, fun β₂ hβ₂ hβ₂1 Δ hΔ => ?_⟩
  · obtain ⟨hθ, hΓ, hθΓ, -, hΞ, hat, -, hS, hSΞ, -, he, -, heΓ, -, hcj⟩ := hj j
    refine ⟨hθ, hΓ, hθΓ, hΞ, hat, hS, hSΞ, he, heΓ, hcj, ?_⟩
    fin_cases j
    exacts [hcw₀, hcw₁, hcw₂]
  obtain ⟨η₁, hη₁, hrow1'⟩ := hrow1 Δ hΔ
  have hΔ1 : 1 ≤ Δ := by linarith only [hΔ]
  obtain ⟨Lc₁, η₀₁, hLc₁, hη₀₁, hrowE⟩ := fc27_edge_test_pp_GAF4 (Γ := Γ 1) (Sg := S 1) (eg := eg 1)
    hΔ1 hβ₂ hβ₂1 ⟨hΓ₁, hΓ1₁⟩ hS₁ (lt_min hSΓ₁ hSC₁) he₁ (lt_min he1₁ (lt_min heΓ₁ heS₁))
  obtain ⟨θs, hθs, hθs1, Lc₂, η₀₂, hLc₂, hη₀₂, hrowS⟩ :=
    fc27_slim_test_pp_C14_GAF4 hΔ1 hβ₂ (by linarith only [hβ₂1]) hΓ₂ hΓ1₂ hS₂ hSΓ₂ hSC₂ he₂ he1₂
        heΓ₂
  refine ⟨η₁, Lc₁, η₀₁, θs, Lc₂, η₀₂, hη₁, hLc₁, hη₀₁, hθs, hθs1, hLc₂, hη₀₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26
        f27 f28 f29 f30 f31
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
    m1 m2 m3 m4 m5 m6 m7 m8 hεr0 sel hsel
  obtain ⟨plane₀, hp₀⟩ := hrow1' P f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
    (f17.trans (min_le_left _ _)) f18 (f19.trans (min_le_left _ _)) f20 f21 f22 f23 f24 f25 f26
    f27 f28 f29 f30 f31
  obtain ⟨plane₁, hp₁⟩ := hrowE X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz P d1 d2 d3 d4 f1 f4 f2 f3 d5 d6 f23 d7 d8 f6 f7 f29 f26 d9 d10 d11
  obtain ⟨plane₂, hp₂⟩ := hrowS X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz P m1 m2 m3 f1 f4 f6 f7 f29 f23 m4 m5 f26 m6 m7 m8
  have he8 : e ≤ 1 / 8 := by linarith only [f6]
  have O₀ := (hout₀ P f1 hΔ1 f2 f3 he8 f4 (sel 0) (hsel 0) (S 0) hS₀ (hmo 0)
    plane₀ (fun x hx => (hp₀.1 x hx).1) (hp₀.2.1 (sel 0) (hsel 0))).some
  have O₁ := (hout₁ P f1 hΔ1 f2 f3 he8 f4 (sel 1) (hsel 1) (S 1) hS₁ (hmo 1)
    plane₁ (fun x hx => (hp₁.1 x hx).1) (hp₁.2.1 (sel 1) (hsel 1))).some
  have O₂ := (hout₂ P f1 hΔ1 f2 f3 he8 f4 (sel 2) (hsel 2) (S 2) hS₂ (hmo 2)
    plane₂ (fun x hx => (hp₂.1 x hx).1) (hp₂.2.1 (sel 2) (hsel 2))).some
  have hθt2 : θt ^ 2 < 1 := by nlinarith only [mul_lt_mul_of_pos_left hθt1 hθt, hθt1]
  refine ⟨{
    std := ⟨f1, hΔ1, f2, f3, f4, f5, f6, f7, f23.le, by linarith only [f24, hθt2],
      ⟨f10, by linarith only [f11, hθt2]⟩, ⟨f18.le, f19.trans (min_le_right _ _)⟩,
      ⟨hεr0, by linarith only [f28, hθt1]⟩⟩
    numbers := hnum
    sel := sel
    hsel := hsel
    plane := ![plane₀, plane₁, plane₂]
    test0 := hp₀
    test1 := hp₁
    test2 := hp₂
    slot := fun st => match st with
      | ⟨0, _⟩ => .active O₀
      | ⟨1, _⟩ => .active O₁
      | ⟨2, _⟩ => .active O₂
      | ⟨k + 3, hk⟩ => absurd hk (by omega) }, rfl⟩

end DifferentialGeometry.Geometry.Collapse
