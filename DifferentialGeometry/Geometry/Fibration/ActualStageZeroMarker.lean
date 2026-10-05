import DifferentialGeometry.Geometry.Metric.ActualStageMarkersUnrolled
import DifferentialGeometry.Geometry.Fibration.ActualStageCloudInputsApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageOneStep
import DifferentialGeometry.Geometry.Fibration.ActualStageCutoffs

/-!
# CFS31's zero-marker input (ZM) at GAF02's stage-one output (CFS29/CFS30, prefix contract)

Blueprint `master207B.tex`, GAF02 (B:5797) proof with CFS31 (B:3783–3855): after stage one,
CFS29/CFS30 PROVE the zero-marker input of the edge and slim cutoffs at `g₁ = Ψ₁ ∘ 𝓔⁰` from the
stage-one prefix alone (no later stage is used). On the actual marker data of `𝓔⁰`
(`v_a = blockMarkerCLM (tag a)`, `R_a = ρ(c_a)`, `ζ_a = cgpMarkerCutoff a`) with the cloud inputs
`gafStage_marker_inputs_GAF5` and stage one's localization `gaf02_stageOne_loc_GAF5`:

* `gafMarker_data_GAF7`: `0 ≤ ζ_a`, `v_a(𝓔⁰) = R_a ζ_a`, and `ζ_a > 0 ⇒ 3R_a/4 ≤ ρ ≤ 5R_a/4`.
* `gaf02_stageOne_zeroMarker_GAF7`: for a `Q₁`-valued stage projection with CFS31's `hnear` on the
  first cloud and `‖g₁ − 𝓔⁰‖ ≤ cρ`, `0 ≤ c ≤ 1/512`: every marker with `ρ(c_a) < ρ/16` vanishes
  at `g₁`, and (AM0) `ζ_a(p) = 0 ⇒ |v_a| ≤ R_a/32` holds on the segment `[𝓔⁰ p, g₁ p]`.
* `gaf02_stageOne_edgeZM_GAF7`: (AM0) at `g₁` in the edge- and slim-family forms taken by
  `gaf02_stageTwo_step_GAF6` / `gaf02_stageThree_step_GAF6`.
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
local instance instMetricN_GAF7z
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF7z
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF7z
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The retained-marker data of `𝓔⁰` in CFS30's form: `0 ≤ ζ_a`, `v_a(𝓔⁰ p) = R_a ζ_a(p)`, and
`ζ_a(p) > 0 ⇒ 3R_a/4 ≤ ρ(p) ≤ 5R_a/4` (`v_a = blockMarkerCLM (tag a)`, `R_a = ρ(c_a)`). -/
theorem gafMarker_data_GAF7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hσs : 0 ≤ σs)
    (hσs1 : σs ≤ 1 / 100) :
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p, 0 ≤ cgpMarkerCutoff P.toLocalChartFamily a p) ∧
      (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a)
          (cgpGlobalMap P.toLocalChartFamily P.zero p) =
          ρ (cgpMarkerCentre P.toLocalChartFamily a) * cgpMarkerCutoff P.toLocalChartFamily a p) ∧
      ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p, 0 < cgpMarkerCutoff P.toLocalChartFamily a p →
        3 / 4 * ρ (cgpMarkerCentre P.toLocalChartFamily a) ≤ ρ p ∧
          ρ p ≤ 5 / 4 * ρ (cgpMarkerCentre P.toLocalChartFamily a) := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  refine ⟨fun a p => (cgpMarkerCutoff_mem_Icc_GAF2 P.toLocalChartFamilyQ hΔ0 a p).1,
    fun a p => (cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero a p).2, ?_⟩
  intro a p hp
  have h := cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ hsmall a p hp
  constructor <;> linarith [h.1, h.2]

/-- **(ZM) at the stage-one output, prefix contract** (CFS29/CFS30 for stage one on the actual
data): with a `Q₁`-valued stage projection `P₁` satisfying CFS31's `hnear` on the first cloud and
`‖g₁ − 𝓔⁰‖ ≤ cρ` with `0 ≤ c ≤ 1/512` (`g₁ = Ψ₁ ∘ 𝓔⁰`, `Ψ₁ = adjustmentMap Q₁ P₁ ψ₁`), every
retained marker with `ρ(c_a) < ρ(q)/16` vanishes at `g₁ q`, and every marker with `ζ_a(p) = 0`
has `|v_a| ≤ ρ(c_a)/32` on the segment from `𝓔⁰ p` to `g₁ p`. -/
theorem gaf02_stageOne_zeroMarker_GAF7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0)
        (sel x) = x)
    (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hPstQ : ∀ z, Pst z ∈ gafStageQ P.toLocalChartFamily P.zero 0) {sg : ℝ} (hsg : 0 < sg)
    (hnear : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 0, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q,
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (Pst z) = 0)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 512)
    (hcum : ∀ q, ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
        (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
          (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q) -
        cgpGlobalMap P.toLocalChartFamily P.zero q‖ ≤ c * ρ q) :
    (∀ q (a : CGPMarkerIndex P.toLocalChartFamily),
      ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
      blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero q)) = 0) ∧
    ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p)),
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) z| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 := by
  have hdat := gafMarker_data_GAF7 P hΛ hΔ hLΛ hσs hσs1
  have hin := gafStage_marker_inputs_GAF5 P hΔ hΛ hLΛ 0 sel hsel
  have hloc0 := gaf02_stageOne_loc_GAF5 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  have key := stage_markers_one_GAF7
    (fun a => blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (cgpMarkerTag P.toLocalChartFamily P.zero a))
    (fun _ => norm_blockMarkerCLM_le _) (fun a => ρ (cgpMarkerCentre P.toLocalChartFamily a))
    (fun _ => hρ _) ρ (cgpMarkerCutoff P.toLocalChartFamily) hdat.1
    (cgpGlobalMap P.toLocalChartFamily P.zero) hdat.2.1 hdat.2.2
    (gafStageQ P.toLocalChartFamily P.zero 0) Pst hPstQ
    (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
      (gafCircleMarker P)) hin.1 (gafCloud P.toLocalChartFamily P.zero 0) sel hin.2.1
    hin.2.2.1 hin.2.2.2 hsg (fun q hq => hloc0 q (subset_tsupport _
      (Function.mem_support.mpr (by convert hq using 2)))) hnear hc0 hc
    (fun q => by convert hcum q using 1)
  refine ⟨fun q a ha => ?_, fun a p hp z hz => ?_⟩
  · convert key.1 q a ha using 2
  · convert key.2 a p hp z hz using 2

/-- The edge- and slim-family forms of (ZM) at a map `f` (the inputs of
`gaf02_stageTwo_step_GAF6` and `gaf02_stageThree_step_GAF6`) from the retained-marker form. -/
theorem gaf02_familyZM_GAF7
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hZM : ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (f p)| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) :
    (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) ∧
    ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32 :=
  ⟨fun j p h => hZM (.inr (.inr j)) p h, fun j p h => hZM (.inr (.inl j)) p h⟩

end DifferentialGeometry.Geometry.Collapse
