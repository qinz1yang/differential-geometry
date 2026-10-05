import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTestPP
import DifferentialGeometry.Geometry.Fibration.ActualStageNearApplications

/-!
# CFS31's `hnear` on the actual first stage (consumer of the first-cloud test with (PP))

* `gaf02_first_stage_hnear_GAF5`: GAF01's stage nearest maps (`gaf01_row_nearest_GAF3`) with the
  first-cloud planes of `fc27_first_test_pp_GAF5` give the first stage projection
  `P₁ = π_{Q₁} ∘ a` with all of `stage_projection_of_nearest_GAF3`'s properties AND CFS31's `hnear`
  at stage one (`gafStage_hnear_GAF4` at `st = 0`). Together with `gaf02_slim_stage_hnear_GAF4`
  (stage three) and the edge test with (PP), `hnear` is now available at all three stages.
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
local instance instMetricNC14_GAF5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF5c {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **Consumer: GAF02's first stage projection with CFS31's `hnear`.** With GAF01's moduli `θ, Ξ`
(with nearest maps): for every `0 < Γ < min(1, θ₁)`, (TP) `0 < Σ < min(Γ/200, Γ³/(100C))` with
`Σ ≤ Ξ₁(Γ)/640`, `0 < e < min(1/100, ΓΣ/100)`, there are TCP06's thresholds such that on the final
family with TCP06's hypotheses (verbatim), for every selection of preimages over `S̃₁` there are
planes (FC27's first test with (PP), inside `Q₁`) and a stage projection `P₁` with values in `Q₁`,
smooth on `Ω = ⋃_{x ∈ S₁} B(x, r_x)`, with `‖P₁ z − (x + Π_x(z − x))‖ ≤ Ξr_x`,
`‖DP₁(z) − Π_x‖ ≤ Ξ` on every `B(x, r_x)`, the adjustment's value step, and CFS31's `hnear`: for
every `x ∈ S₁`, `z ∈ B(x, r_x)`, preimage `q` of `x` and retained marker with `ρ(c_a) < ρ(q)/16`,
the marker `v_a(P₁ z)` vanishes. -/
theorem gaf02_first_stage_hnear_GAF5 (Kj : ℕ) {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ), 0 < θ 0 ∧
      ∀ Γ sg eg : ℝ, 0 < Γ → Γ < 1 → Γ < θ 0 → 0 < sg → sg < Γ / 200 →
        sg < Γ ^ 3 / (100 * tcpGraphConst) → sg ≤ Ξ 0 Γ / 640 → 0 < eg → eg < 1 / 100 →
        eg < Γ * sg / 100 →
        ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θt : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θt ∧
        θt < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
        ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
          [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
          {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
          {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
          {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
          (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
            εr e T V vs ζ Λz),
          0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
          4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
          0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θt ^ 2 / 1000 → μ * Δ ≤ θt / 100 →
          3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ →
          βc ≤ ηc → b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θt ^ 2 / 1000 → vs ≤ θt / 100 → 0 < ζ →
          ζ ≤ θt ^ 2 / 1000 → εr ≤ θt / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
          1000 * tcpGraphConst * Δ * Λ < eg →
          ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
            cgpProjMap P.toLocalChartFamily P.zero
              (gafStageTags P.toLocalChartFamily P.zero 0) (sel x) = x) →
          ∃ (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
              Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
            (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
              BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
            (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
              Module.finrank ℝ (plane x) = gafStageDim 0 ∧
                plane x ≤ gafStageQ P.toLocalChartFamily P.zero 0) ∧
            (∀ z, Pst z ∈ gafStageQ P.toLocalChartFamily P.zero 0) ∧
            ContDiffOn ℝ ∞ Pst (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
              ball x (sg * ρ (sel x))) ∧
            (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)),
              ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ 0 Γ * (sg * ρ (sel x)) ∧
              DifferentiableAt ℝ Pst z ∧
              ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ 0 Γ ∧
              ∀ (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
                (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                ψ y ∈ Icc (0 : ℝ) 1 →
                (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = z →
                ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst ψ y - y‖ ≤
                  Ξ 0 Γ * (sg * ρ (sel x)) + ‖z - x‖) ∧
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q,
              (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
                  (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
              ∀ a : CGPMarkerIndex P.toLocalChartFamily,
                ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
                blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (Pst z) = 0 := by
  obtain ⟨θ, Ξ, hnear, -⟩ := gaf01_row_nearest_GAF3 Kj
  refine ⟨θ, Ξ, (hnear 0).1, fun Γ sg eg hΓ hΓ1 hθΓ hsg hsgΓ hsgC hsgΞ heg heg1 hegΓ => ?_⟩
  have hst := (hnear 0).2.2 Γ hΓ hθΓ
  obtain ⟨hΞ, -, hmain⟩ := hst
  have hmo : 128 * (Ξ 0 Γ)⁻¹ * sg ≤ 1 / 5 := by
    have h1 : 128 * (Ξ 0 Γ)⁻¹ * sg ≤ 128 * (Ξ 0 Γ)⁻¹ * (Ξ 0 Γ / 640) :=
      mul_le_mul_of_nonneg_left hsgΞ (by positivity)
    have h2 : 128 * (Ξ 0 Γ)⁻¹ * (Ξ 0 Γ / 640) = 1 / 5 := by
      field_simp
      norm_num
    linarith
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, hrow⟩ :=
    fc27_first_test_pp_GAF5 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hν hν1
  refine ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θt, hη₂, hγ₀, hηc, hθt, hθt1, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, h⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31 sel hsel
  have hP := h P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
    h23 h24 h25 h26 h27 h28 h29 h30 h31
  refine hP.elim fun plane hpl => ?_
  have hdimQ := hpl.1
  have hcloud := hpl.2.1
  have hpp := hpl.2.2.2
  have hΔ1 : 1 ≤ Δ := by linarith
  have ha := hmain X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P h1 hΔ1 h2 h3 (by linarith) h4 sel hsel sg hsg hsgΞ plane (fun x hx => (hdimQ x hx).1)
    (hcloud sel hsel)
  refine ha.elim fun a hpa => ?_
  have hproj := stage_projection_of_nearest_GAF3 (gafStageQ P.toLocalChartFamily P.zero 0)
    (gafCloud P.toLocalChartFamily P.zero 0) (fun x => sg * ρ (sel x)) plane a
    (fun x hx => gafCloud_subset_gafStageQ P.toLocalChartFamily P.zero 0 hx)
    (fun x hx => (hdimQ x hx).2) hpa.1
    (fun x hx z hz => ⟨(hpa.2 x hx z hz).1, (hpa.2 x hx z hz).2.1, (hpa.2 x hx z hz).2.2.1⟩)
  have hnr := gafStage_hnear_GAF4 P.toLocalChartPackets hΔ1 h1 h4 0 sel hsel hsg hΞ hmo plane hpp
    a (fun x hx z hz => (hpa.2 x hx z hz).2.2.2)
  exact ⟨plane, _, hdimQ, hproj.1, hproj.2.1, hproj.2.2, hnr⟩

end DifferentialGeometry.Geometry.Collapse
