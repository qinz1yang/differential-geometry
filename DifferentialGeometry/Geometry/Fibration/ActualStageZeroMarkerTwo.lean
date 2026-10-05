import DifferentialGeometry.Geometry.Fibration.ActualStageZeroMarkerApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageTwoThreeStep

/-!
# (ZM) at GAF02's stage-two output and (AM0) on the segment to `E` (CFS29/CFS30, prefix contracts)

Blueprint `master207B.tex`, GAF02 (B:5797) with CFS31 (B:3783–3855). The zero-marker inputs of the
later cutoffs come from PREFIX contracts only:

* `gaf02_stageTwo_zeroMarker_GAF7` (two stages, `g₂ = Ψ₂ ∘ g₁`): stage two's localization is
  CFS23's closed-support clause at `g₁` (`gaf02_stageTwo_cutoff_point_GAF6`, fed by the stage-one
  (ZM) `gaf02_stageOne_edgeZM_GAF7` and `‖g₁ − 𝓔⁰‖ ≤ c₀ρ ≤ (4κ/5)ρ`); with `c₀ ≤ 3Σ₂/10`,
  `‖g₂ − 𝓔⁰‖ ≤ c₁ρ`, `c₁ ≤ 1/512`: small markers vanish at `g₁`, `g₂`, and (AM0) holds on
  `[𝓔⁰ p, g₂ p]`.
* `gaf02_stageThree_zeroMarker_GAF7` (three stages, `E = Ψ₃ ∘ g₂`): the same with stage three's
  localization from CFS22's clause at `g₂`; (AM0) on `[𝓔⁰ p, E p]` (GAF02's segment assertion).
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF7t2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF7t2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF7t2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **(ZM) at the stage-two output, prefix contract** (CFS29/CFS30 for stages one and two on
the actual data): small markers vanish at `g₁` and `g₂`, and (AM0) holds on `[𝓔⁰ p, g₂ p]`. -/
theorem gaf02_stageTwo_zeroMarker_GAF7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (sel₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₀ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel₀ x) = x)
    (P₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hP₀ : ∀ z, P₀ z ∈ gafStageQ P.toLocalChartFamily P.zero 0)
    {sg₀ : ℝ} (hsg₀ : 0 < sg₀)
    (hnear₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∀ z ∈ ball x (sg₀ * ρ (sel₀ x)), ∀ q, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (P₀ z) = 0)
    (sel₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₁ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel₁ x) = x)
    (P₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hP₁ : ∀ z, P₁ z ∈ gafStageQ P.toLocalChartFamily P.zero 1)
    {sg₁ : ℝ} (hsg₁ : 0 < sg₁)
    (hnear₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      ∀ z ∈ ball x (sg₁ * ρ (sel₁ x)), ∀ q, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (P₁ z) = 0)
    {c₀ c₁ : ℝ} (hc₀0 : 0 ≤ c₀) (hc₀ : c₀ ≤ 1 / 512) (hc₀κ : c₀ ≤ 4 * gafKappa / 5)
    (hc₀s : c₀ ≤ 3 * sg₁ / 10) (hc₁0 : 0 ≤ c₁) (hc₁ : c₁ ≤ 1 / 512)
    (hcum₁ : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q) -
        cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₀ * ρ q)
    (hcum₂ : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)) -
        cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₁ * ρ q) :
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q))) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p))),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  have hdat := gafMarker_data_GAF7 P hΛ hΔ hLΛ hσs hσs1
  have hin₀ := gafStage_marker_inputs_GAF5 P hΔ hΛ hLΛ 0 sel₀ hsel₀
  have hin₁ := gafStage_marker_inputs_GAF5 P hΔ hΛ hLΛ 1 sel₁ hsel₁
  have hloc0 := gaf02_stageOne_loc_GAF5 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  have hzm := gaf02_stageOne_edgeZM_GAF7 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₀ hsel₀ P₀ hP₀
    hsg₀ hnear₀ hc₀0 hc₀ hcum₁
  have hpert : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q) -
      cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q := fun q =>
    (hcum₁ q).trans (mul_le_mul_of_nonneg_right hc₀κ (hρ q).le)
  have hloc1 := fun q =>
    (gaf02_stageTwo_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 _ hpert hzm.2.1 q).1
  have key := stage_markers_two_GAF7
    (fun a => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a))
    (fun _ => norm_blockMarkerCLM_le _) (fun a => ρ (cgpMarkerCentre P.toLocalChartFamily a))
    (fun _ => hρ _) ρ (cgpMarkerCutoff P.toLocalChartFamily) hdat.1
    (cgpGlobalMap P.toLocalChartFamily P.zero) hdat.2.1 hdat.2.2
    (gafStageQ P.toLocalChartFamily P.zero 0) (gafStageQ P.toLocalChartFamily P.zero 1) P₀ P₁
    hP₀ hP₁
    (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P))
    (gafStageTwoCutoff P.toLocalChartFamily P.zero)
    hin₀.1 hin₁.1 (gafCloud P.toLocalChartFamily P.zero 0)
    (gafCloud P.toLocalChartFamily P.zero 1)
    sel₀ sel₁ hin₀.2.1 hin₁.2.1 hin₀.2.2.1 hin₁.2.2.1 hin₀.2.2.2 hin₁.2.2.2 hsg₀ hsg₁ hc₀s
    (fun q hq => hloc0 q (subset_tsupport _
      (Function.mem_support.mpr (by convert hq using 2))))
    (fun q hq => hloc1 q (subset_tsupport _
      (Function.mem_support.mpr (by convert hq using 2))))
    (fun q => by convert hcum₁ q using 1) hnear₀ hnear₁ hc₁0 hc₁
    (fun q => by convert hcum₂ q using 1)
  refine ⟨fun q a ha => ?_, fun q a ha => ?_, fun a p hp z hz => ?_⟩
  · convert key.1 q a ha using 2
  · convert key.2.1 q a ha using 2
  · convert key.2.2 a p hp z hz using 2

/-- **(AM0) on the segment to `E`, prefix contract for three stages** (CFS29/CFS30 on the actual
data): stage three's localization is CFS22's closed-support clause at `g₂`, fed by the stage-two
(ZM) of `gaf02_stageTwo_zeroMarker_GAF7`; small markers vanish at `g₁`, `g₂`, `E = g₃`, and (AM0)
holds on `[𝓔⁰ p, E p]`. -/
theorem gaf02_stageThree_zeroMarker_GAF7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (sel₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₀ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel₀ x) = x)
    (P₀ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hP₀ : ∀ z, P₀ z ∈ gafStageQ P.toLocalChartFamily P.zero 0)
    {sg₀ : ℝ} (hsg₀ : 0 < sg₀)
    (hnear₀ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0,
      ∀ z ∈ ball x (sg₀ * ρ (sel₀ x)), ∀ q, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (P₀ z) = 0)
    (sel₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₁ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 1,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1)
        (sel₁ x) = x)
    (P₁ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hP₁ : ∀ z, P₁ z ∈ gafStageQ P.toLocalChartFamily P.zero 1)
    {sg₁ : ℝ} (hsg₁ : 0 < sg₁)
    (hnear₁ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 1,
      ∀ z ∈ ball x (sg₁ * ρ (sel₁ x)), ∀ q, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (P₁ z) = 0)
    (sel₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel₂ : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2)
        (sel₂ x) = x)
    (P₂ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hP₂ : ∀ z, P₂ z ∈ gafStageQ P.toLocalChartFamily P.zero 2)
    {sg₂ : ℝ} (hsg₂ : 0 < sg₂)
    (hnear₂ : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
      ∀ z ∈ ball x (sg₂ * ρ (sel₂ x)), ∀ q, (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (P₂ z) = 0)
    {c₀ c₁ c₂ : ℝ} (hc₀0 : 0 ≤ c₀) (hc₀ : c₀ ≤ 1 / 512) (hc₀κ : c₀ ≤ 4 * gafKappa / 5)
    (hc₀s : c₀ ≤ 3 * sg₁ / 10) (hc₁0 : 0 ≤ c₁) (hc₁ : c₁ ≤ 1 / 512) (hc₁κ : c₁ ≤ 4 * gafKappa / 5)
    (hc₁s : c₁ ≤ 3 * sg₂ / 10) (hc₂0 : 0 ≤ c₂) (hc₂ : c₂ ≤ 1 / 512)
    (hcum₁ : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q) -
        cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₀ * ρ q)
    (hcum₂ : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)) -
        cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₁ * ρ q)
    (hcum₃ : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) P₂
        (gafStageThreeCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
         (gafStageTwoCutoff P.toLocalChartFamily P.zero)
         (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q))) -
        cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c₂ * ρ q) :
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q))) = 0) ∧
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) P₂
        (gafStageThreeCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
         (gafStageTwoCutoff P.toLocalChartFamily P.zero)
         (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)))) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) P₂
        (gafStageThreeCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
         (gafStageTwoCutoff P.toLocalChartFamily P.zero)
         (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p)))),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  have hdat := gafMarker_data_GAF7 P hΛ hΔ hLΛ hσs hσs1
  have hin₀ := gafStage_marker_inputs_GAF5 P hΔ hΛ hLΛ 0 sel₀ hsel₀
  have hin₁ := gafStage_marker_inputs_GAF5 P hΔ hΛ hLΛ 1 sel₁ hsel₁
  have hin₂ := gafStage_marker_inputs_GAF5 P hΔ hΛ hLΛ 2 sel₂ hsel₂
  have hloc0 := gaf02_stageOne_loc_GAF5 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  have hzm := gaf02_stageOne_edgeZM_GAF7 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₀ hsel₀ P₀ hP₀
    hsg₀ hnear₀ hc₀0 hc₀ hcum₁
  have hpert : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q) -
      cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q := fun q =>
    (hcum₁ q).trans (mul_le_mul_of_nonneg_right hc₀κ (hρ q).le)
  have hloc1 := fun q =>
    (gaf02_stageTwo_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 _ hpert hzm.2.1 q).1
  have h2 := gaf02_stageTwo_zeroMarker_GAF7 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel₀ hsel₀ P₀ hP₀
    hsg₀ hnear₀ sel₁ hsel₁ P₁ hP₁ hsg₁ hnear₁ hc₀0 hc₀ hc₀κ hc₀s hc₁0 hc₁ hcum₁ hcum₂
  have hZM2 : ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p)))| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 :=
    fun a p hp => h2.2.2 a p hp _ (right_mem_segment ℝ _ _)
  have hfam := gaf02_familyZM_GAF7 P _ hZM2
  have hpert2 : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 1) P₁
        (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) P₀
         (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
           (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)) -
      cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ 4 * gafKappa / 5 * ρ q := fun q =>
    (hcum₂ q).trans (mul_le_mul_of_nonneg_right hc₁κ (hρ q).le)
  have hloc2 := fun q =>
    (gaf02_stageThree_cutoff_point_GAF6 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 _ hpert2 hfam.2 q).1
  have key := stage_markers_three_GAF7
    (fun a => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a))
    (fun _ => norm_blockMarkerCLM_le _) (fun a => ρ (cgpMarkerCentre P.toLocalChartFamily a))
    (fun _ => hρ _) ρ (cgpMarkerCutoff P.toLocalChartFamily) hdat.1
    (cgpGlobalMap P.toLocalChartFamily P.zero) hdat.2.1 hdat.2.2
    (gafStageQ P.toLocalChartFamily P.zero 0) (gafStageQ P.toLocalChartFamily P.zero 1)
    (gafStageQ P.toLocalChartFamily P.zero 2) P₀ P₁ P₂ hP₀ hP₁ hP₂
    (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P))
    (gafStageTwoCutoff P.toLocalChartFamily P.zero)
    (gafStageThreeCutoff P.toLocalChartFamily P.zero)
    hin₀.1 hin₁.1 hin₂.1 (gafCloud P.toLocalChartFamily P.zero 0)
    (gafCloud P.toLocalChartFamily P.zero 1) (gafCloud P.toLocalChartFamily P.zero 2)
    sel₀ sel₁ sel₂ hin₀.2.1 hin₁.2.1 hin₂.2.1 hin₀.2.2.1 hin₁.2.2.1 hin₂.2.2.1 hin₀.2.2.2
    hin₁.2.2.2 hin₂.2.2.2 hsg₀ hsg₁ hsg₂ hc₀s hc₁s
    (fun q hq => hloc0 q (subset_tsupport _
      (Function.mem_support.mpr (by convert hq using 2))))
    (fun q hq => hloc1 q (subset_tsupport _
      (Function.mem_support.mpr (by convert hq using 2))))
    (fun q hq => hloc2 q (subset_tsupport _
      (Function.mem_support.mpr (by convert hq using 2))))
    (fun q => by convert hcum₁ q using 1) (fun q => by convert hcum₂ q using 1)
    hnear₀ hnear₁ hnear₂ hc₂0 hc₂ (fun q => by convert hcum₃ q using 1)
  refine ⟨fun q a ha => ?_, fun q a ha => ?_, fun q a ha => ?_, fun a p hp z hz => ?_⟩
  · convert key.1 q a ha using 2
  · convert key.2.1 q a ha using 2
  · convert key.2.2.1 q a ha using 2
  · convert key.2.2.2 a p hp z hz using 2

end DifferentialGeometry.Geometry.Collapse
