import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTest
import DifferentialGeometry.Geometry.Fibration.ActualStageEdgeTest
import DifferentialGeometry.Geometry.Fibration.ActualStageSlimTestApplications

/-!
# FC27 on the actual clouds: the three stage tests assembled

Blueprint `master207B.tex`, FC27 (`found:fibration-projected-clouds`, B:1658) in the frozen form of
`sheet-C14-GAF2.md` (`fc27_row_GAF2`), with the amendment `plane st x ≤ gafStageQ st` recorded in
`state-C14-GAF2.md` (needed for GAF02's `P_j = π_{Q_j} ∘ p_j`).

For every stage `st : Fin 3` (`0` first cloud / TCP06, `1` edge / EGP07, `2` slim / SGP06) with
GAF01's early ranges `0 < Γ_st < 1`, `0 < Σ_st < min(Γ_st/200, Γ_st³/(100 C_st))`,
`0 < e_st < min(1/100, Γ_stΣ_st/100, Σ_st/1000)` (`C = gafGraphConst`), the thresholds of the three
rows (TCP06: `σ, η₂, γ₀, ηc, θ, η₁`; SGP06: `θs, Lc, η₀`; EGP07: `Lc', η₀'`) are produced, and on
every `LocalChartPacketsC14` with the union of the three rows' hypotheses (each distinct clause
once, verbatim), for every selection `sel st` of preimages over `S̃_st`, there are planes over every
stage cloud `S_st = gafCloud st` of dimension `gafStageDim st`, inside `Q_st`, with the (CS) test at
quality `Γ_st` and radius `Σ_st ρ(sel st x)`.

The rows' rank clauses are in the three stage tests (`fc27_first_test_GAF4`, `fc27_edge_test_GAF3`,
`fc27_slim_test_C14_GAF3`), not in FC27's frozen conclusion.
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
local instance instMetricNC14_GAF4a {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF4a {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF4a {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27 on the actual clouds** (frozen form of `sheet-C14-GAF2.md` with the amendment
`plane st x ≤ gafStageQ st`). For `Δ ≥ 1200`, `0 < β₂ < 10⁻⁶`, `0 < ν < 1` and GAF01's early
ranges of `Γ, Σ, e : Fin 3 → ℝ` there are the thresholds of TCP06, SGP06 and EGP07 such that on
every actual `LocalChartPacketsC14` with the union of the three rows' hypotheses (TCP06's, then
SGP06's and EGP07's clauses not already listed) and for every selection of preimages over the
enlarged stage clouds there are planes `plane st x` over every stage cloud with
`dim = gafStageDim st`, `plane st x ≤ Q_st` and the (CS) test
`hausdorffEDist (S̃_st ∩ B(x, r/Γ_st)) ((x + plane st x) ∩ B(x, r/Γ_st)) ≤ Γ_st r`,
`r = Σ_st ρ(sel st x)`. -/
theorem fc27_row_GAF2 {Δ β₂ ν : ℝ} (hΔ : 1200 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hν : 0 < ν) (hν1 : ν < 1) (Γ sg eg : Fin 3 → ℝ) (hΓ : ∀ st, 0 < Γ st ∧ Γ st < 1)
    (hsg : ∀ st, 0 < sg st ∧ sg st < min (Γ st / 200) (Γ st ^ 3 / (100 * gafGraphConst st)))
    (heg : ∀ st, 0 < eg st ∧
      eg st < min (1 / 100) (min (Γ st * sg st / 100) (sg st / 1000))) :
    ∃ σ η₂ γ₀ ηc θ η₁ θs Lc η₀ Lc' η₀' : ℝ,
      (0 < σ ∧ σ ≤ 1 / 1000 ∧ 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧ θ < 1 ∧ 0 < η₁ ∧
        0 < θs ∧ θs < 1 ∧ 0 < Lc ∧ 0 < η₀ ∧ 0 < Lc' ∧ 0 < η₀') ∧
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
  refine ⟨σ, η₂, γ₀, ηc, θ, η₁, θs, Lc, η₀, Lc', η₀',
    ⟨hσ, hσ1, hη₂, hγ₀, hηc, hθ, hθ1, hη₁, hθs, hθs1, hLc, hη₀, hLc', hη₀'⟩, ?_⟩
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
