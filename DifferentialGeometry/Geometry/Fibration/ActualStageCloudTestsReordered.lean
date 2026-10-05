import DifferentialGeometry.Geometry.Fibration.ActualStageCloudTests

/-!
# FC27's packaged row with `β₂` after the first-test thresholds (lane C14-CHAIN-INST, G6)

`fc27_row_GAF2` (`ActualStageCloudTests.lean`) takes `β₂` as a parameter BEFORE its existential
thresholds `σ, η₂`, while its packet premises contain `3 * β 2 ≤ σ`, `β 2 ≤ η₂` and `β 2 = β₂`.
In that order the statement admits the witness `σ = β₂/4`, which makes the premises contradictory:
read as stated, the row can be vacuous (`fc27_row_order_vacuous_CHI` below). The reordered row
`fc27_row_reordered_CHI` quantifies `β₂` after `σ, η₂, γ₀, ηc, θ, η₁` (TCP06's thresholds, which
`fc27_first_test_GAF4` produces from `ν` alone) and before SGP06's and EGP07's thresholds, with the
verbatim hypothesis list and conclusion. The proof is `fc27_row_GAF2`'s.

* `fc27_row_order_vacuous_CHI`: the old order is satisfied by the witness `σ = β₂/4`, `η₂ = 1`,
  for which `3 * β 2 ≤ σ` and `β 2 = β₂` cannot hold together (the minimal counterexample).
* `fc27_row_order_satisfiable_CHI`: in the new order, for every `σ, η₂ > 0` some
  `β₂ ∈ (0, 10⁻⁶)` meets `3β₂ ≤ σ` and `β₂ ≤ η₂`.
* `fc27_row_reordered_CHI`: the reordered row.
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_CHIR {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_CHIR {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_CHIR {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **The old order is vacuous-admitting (minimal counterexample).** In `fc27_row_GAF2`'s order
(`β₂` first, then `∃ σ η₂`), the witnesses `σ = β₂/4`, `η₂ = 1` satisfy the threshold clauses
`0 < σ ≤ 1/1000`, `0 < η₂`, and for them the packet premises `3 * β 2 ≤ σ`, `β 2 ≤ η₂`,
`β 2 = β₂` are contradictory: the row would then hold for every conclusion. -/
theorem fc27_row_order_vacuous_CHI :
    ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 → ∃ σ η₂ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ 0 < η₂ ∧
      ∀ β : ℕ → ℝ, 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 2 = β₂ → False := by
  intro β₂ hβ₂ hβ₂1
  refine ⟨β₂ / 4, 1, by positivity, by linarith, one_pos, fun β h1 _ h3 => ?_⟩
  rw [h3] at h1
  linarith

/-- **The new order is satisfiable**: for every `σ, η₂ > 0` there is `β₂ ∈ (0, 10⁻⁶)` with
`3β₂ ≤ σ` and `β₂ ≤ η₂` (`β₂ = min(σ/3, η₂, 1/(2·10⁶))`). -/
theorem fc27_row_order_satisfiable_CHI {σ η₂ : ℝ} (hσ : 0 < σ) (hη₂ : 0 < η₂) :
    ∃ β₂ : ℝ, 0 < β₂ ∧ β₂ < 1 / 1000000 ∧ 3 * β₂ ≤ σ ∧ β₂ ≤ η₂ := by
  refine ⟨min (min (σ / 3) η₂) (1 / 2000000), by positivity, ?_, ?_, ?_⟩
  · linarith [min_le_right (min (σ / 3) η₂) (1 / 2000000)]
  · linarith [min_le_left (min (σ / 3) η₂) (1 / 2000000), min_le_left (σ / 3) η₂]
  · exact (min_le_left _ _).trans (min_le_right _ _)

/-- **FC27's packaged row, reordered** (`fc27_row_GAF2` with `β₂` quantified after TCP06's
thresholds `σ, η₂, γ₀, ηc, θ, η₁` and before SGP06's / EGP07's `θs, Lc, η₀, Lc', η₀'`; hypotheses
and conclusion verbatim). -/
theorem fc27_row_reordered_CHI {Δ ν : ℝ} (hΔ : 1200 ≤ Δ) (hν : 0 < ν) (hν1 : ν < 1)
    (Γ sg eg : Fin 3 → ℝ) (hΓ : ∀ st, 0 < Γ st ∧ Γ st < 1)
    (hsg : ∀ st, 0 < sg st ∧ sg st < min (Γ st / 200) (Γ st ^ 3 / (100 * gafGraphConst st)))
    (heg : ∀ st, 0 < eg st ∧
      eg st < min (1 / 100) (min (Γ st * sg st / 100) (sg st / 1000))) :
    ∃ σ η₂ γ₀ ηc θ η₁ : ℝ,
      (0 < σ ∧ σ ≤ 1 / 1000 ∧ 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧ θ < 1 ∧ 0 < η₁) ∧
      ∀ β₂ : ℝ, 0 < β₂ → β₂ < 1 / 1000000 →
      ∃ θs Lc η₀ Lc' η₀' : ℝ, (0 < θs ∧ θs < 1 ∧ 0 < Lc ∧ 0 < η₀ ∧ 0 < Lc' ∧ 0 < η₀') ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        -- TCP06
        0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
        3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ →
        βc ≤ ηc → b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
        ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
        1000 * tcpGraphConst * Δ * Λ < eg 0 →
        -- SGP06
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
        ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θs / (100 * (1000000 * Δ)) →
        -- EGP07
        b ≤ η₀' → s < 1 / 1000000 → β 1 ≤ η₀' → Lc' ≤ Lmax →
        σc ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        μ * Δ < eg 1 / (20 * egpGraphConst) / 100 →
        σs ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 →
        vs < eg 1 / (20 * egpGraphConst) / 100 →
        ζ ≤ (eg 1 / (20 * egpGraphConst)) ^ 2 / 10 ^ 8 → ζ ≤ 1 / (1000 * (1000000 * Δ)) →
        εr < eg 1 / (20 * egpGraphConst) / (100 * (1000000 * Δ)) →
        ∀ sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
        (∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
          cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
            (sel st x) = x) →
        ∃ plane : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          ∀ st, ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
            Module.finrank ℝ (plane st x) = gafStageDim st ∧
            plane st x ≤ gafStageQ P.toLocalChartFamily P.zero st ∧
            hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
                ball x (sg st * ρ (sel st x) / Γ st))
              ((AffineSubspace.mk' x (plane st x) :
                  Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                ball x (sg st * ρ (sel st x) / Γ st)) ≤
              ENNReal.ofReal (Γ st * (sg st * ρ (sel st x))) := by
  have hΔ1 : (1 : ℝ) ≤ Δ := by linarith
  -- stage 0: TCP06
  have hm0 := (hsg 0).2
  have he0 := (heg 0).2
  have hsg0Γ : sg 0 < Γ 0 / 200 := lt_of_lt_of_le hm0 (min_le_left _ _)
  have hsg0C : sg 0 < Γ 0 ^ 3 / (100 * tcpGraphConst) := lt_of_lt_of_le hm0 (min_le_right _ _)
  have he01 : eg 0 < 1 / 100 := lt_of_lt_of_le he0 (min_le_left _ _)
  have he0Γ : eg 0 < Γ 0 * sg 0 / 100 :=
    lt_of_lt_of_le he0 ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, hrow0⟩ :=
    fc27_first_test_GAF4 (hΓ 0).1 (hΓ 0).2 (hsg 0).1 hsg0Γ hsg0C (heg 0).1 he01 he0Γ hν hν1
  obtain ⟨η₁, hη₁, h0⟩ := hrow0 Δ hΔ
  refine ⟨σ, η₂, γ₀, ηc, θ, η₁, ⟨hσ, hσ1, hη₂, hγ₀, hηc, hθ, hθ1, hη₁⟩,
    fun β₂ hβ₂ hβ₂1 => ?_⟩
  -- stage 2: SGP06
  have hm2 := (hsg 2).2
  have he2 := (heg 2).2
  have hsg2Γ : sg 2 < Γ 2 / 200 := lt_of_lt_of_le hm2 (min_le_left _ _)
  have hsg2C : sg 2 < Γ 2 ^ 3 / (100 * sgpGraphBound) := lt_of_lt_of_le hm2 (min_le_right _ _)
  have he21 : eg 2 < 1 / 100 := lt_of_lt_of_le he2 (min_le_left _ _)
  have he2Γ : eg 2 < Γ 2 * sg 2 / 100 :=
    lt_of_lt_of_le he2 ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, h2⟩ :=
    fc27_slim_test_C14_GAF3 hΔ1 hβ₂ (by linarith) (hΓ 2).1 (hΓ 2).2 (hsg 2).1 hsg2Γ hsg2C
      (heg 2).1 he21 he2Γ
  -- stage 1: EGP07
  obtain ⟨Lc', η₀', hLc', hη₀', h1⟩ :=
    fc27_edge_test_GAF3 hΔ1 hβ₂ hβ₂1 ⟨(hΓ 1).1, (hΓ 1).2⟩ (hsg 1).1 (hsg 1).2 (heg 1).1 (heg 1).2
  refine ⟨θs, Lc, η₀, Lc', η₀', ⟨hθs, hθs1, hLc, hη₀, hLc', hη₀'⟩, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25
    t26 t27 t28 t29 t30 t31 s1 s2 s3 s4 s5 s6 s7 s8 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 sel hsel
  have T0 := h0 P t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21
    t22 t23 t24 t25 t26 t27 t28 t29 t30 t31
  have T1 := h1 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    e1 e2 e3 e4 t1 t4 t2 t3 e5 e6 t23 e7 e8 t6 t7 t29 t26 e9 e10 e11
  have T2 := h2 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    s1 s2 s3 t1 t4 t6 t7 t29 t23 s4 s5 t26 s6 s7 s8
  have hall : ∀ st : Fin 3, ∃ W : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
        Module.finrank ℝ (W x) = gafStageDim st ∧
        W x ≤ gafStageQ P.toLocalChartFamily P.zero st ∧
        hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
            ball x (sg st * ρ (sel st x) / Γ st))
          ((AffineSubspace.mk' x (W x) :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
            ball x (sg st * ρ (sel st x) / Γ st)) ≤
          ENNReal.ofReal (Γ st * (sg st * ρ (sel st x))) := by
    intro st
    fin_cases st
    · exact T0.elim fun W hW => ⟨W, fun x hx =>
        ⟨(hW.1 x hx).1, (hW.1 x hx).2, hW.2.1 (sel 0) (hsel 0) x hx⟩⟩
    · exact T1.elim fun W hW => ⟨W, fun x hx =>
        ⟨(hW.1 x hx).1, (hW.1 x hx).2, hW.2.1 (sel 1) (hsel 1) x hx⟩⟩
    · exact T2.elim fun W hW => ⟨W, fun x hx =>
        ⟨(hW.1 x hx).1, (hW.1 x hx).2, hW.2.1 (sel 2) (hsel 2) x hx⟩⟩
  choose plane hplane using hall
  exact ⟨plane, hplane⟩

end DifferentialGeometry.Geometry.Collapse
