import DifferentialGeometry.Geometry.Fibration.ActualStageZeroMarker

/-!
# (ZM) at GAF02's stage-one output in the family forms of the next stages

Consumer of `gaf02_stageOne_zeroMarker_GAF7` (CFS29/CFS30 prefix contract at `g₁ = Ψ₁ ∘ 𝓔⁰`,
blueprint `master207B.tex` GAF02 B:5797 with CFS31 B:3783): (AM0) at `g₁` for every retained
marker and in the edge- and slim-family forms that `gaf02_stageTwo_step_GAF6` and
`gaf02_stageThree_step_GAF6` take as their (ZM) input.
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
local instance instMetricN_GAF7za
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF7za
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF7za
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **(ZM) at `g₁` for the next stages**: for every retained marker, and in the edge- and
slim-family forms (`ζ_j(p) = 0 ⇒ |v_j(g₁ p)| ≤ ρ(c_j)/32`). -/
theorem gaf02_stageOne_edgeZM_GAF7
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
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p))| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32) ∧
    (∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p))| ≤ ρ j.1 / 32) ∧
    ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p))| ≤ ρ j.1 / 32 := by
  have h := gaf02_stageOne_zeroMarker_GAF7 P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 sel hsel Pst
    hPstQ hsg hnear hc0 hc hcum
  have hZM : ∀ (a : CGPMarkerIndex P.toLocalChartFamily) p,
      cgpMarkerCutoff P.toLocalChartFamily a p = 0 →
      |blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 0) Pst
          (markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1) (gafCircleVector P)
            (gafCircleMarker P)) (cgpGlobalMap P.toLocalChartFamily P.zero p))| ≤
        ρ (cgpMarkerCentre P.toLocalChartFamily a) / 32 :=
    fun a p hp => h.2 a p hp _ (right_mem_segment ℝ _ _)
  have hfam := gaf02_familyZM_GAF7 P _ hZM
  exact ⟨hZM, hfam.1, hfam.2⟩

end DifferentialGeometry.Geometry.Collapse
