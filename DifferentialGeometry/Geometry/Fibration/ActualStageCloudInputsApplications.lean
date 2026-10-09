import DifferentialGeometry.Geometry.Fibration.ActualStageCloudInputs

/-!
# CFS31's marker inputs at one actual stage (consumer)

* `gafStage_marker_inputs_GAF5`: at every stage `st` of the actual `𝓔⁰` on `LocalChartPackets`
  (`1 ≤ Δ`, `0 ≤ Λ`, `10⁶ΔΛ < 10⁻⁵`) and for every selection of preimages over `S̃_st`: CFS31's
  `hretained` (`blockMarker_retained_GAF4`), `hsupport` (`gafStage_support_GAF4`), `hfullS`
  (`gafStage_fullS_GAF5`) and `hselect` (`gafStage_select_GAF5`) with `v_a = (·)_{tag a}.snd`,
  `R_a = ρ(c_a)`, `Q = gafStageQ st`, `S = gafCloud st`.
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
local instance instMetricN_GAF5j
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF5j
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF5j
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS31's marker inputs at one actual stage**: `hretained`, `hsupport`, `hfullS`, `hselect`
for `Q = gafStageQ st`, `S = gafCloud st`, `v_a = (·)_{tag a}.snd`, `R_a = ρ(c_a)`, `F = 𝓔⁰` and
any selection of preimages over `S̃_st`. -/
theorem gafStage_marker_inputs_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        (sel x) = x) :
    (∀ a : CGPMarkerIndex P.toLocalChartFamily,
      (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ ≤
        gafStageQ P.toLocalChartFamily P.zero st ∨
      (LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (cgpMarkerTag P.toLocalChartFamily P.zero a) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))ᗮ ≤
        (gafStageQ P.toLocalChartFamily P.zero st)ᗮ) ∧
    (∀ (a : CGPMarkerIndex P.toLocalChartFamily) q,
      0 < blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
        ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q)) →
      3 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4 ≤ ρ q ∧
        ρ q ≤ 5 * ρ (cgpMarkerCentre P.toLocalChartFamily a) / 4) ∧
    (∀ q, (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero q) ∈ gafCloud P.toLocalChartFamily P.zero st →
      ∃ a : CGPMarkerIndex P.toLocalChartFamily,
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
          ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q)) =
          ρ (cgpMarkerCentre P.toLocalChartFamily a)) ∧
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero (sel x)) = x := by
  classical
  have hΔ0 : 0 ≤ Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  exact ⟨fun a => blockMarker_retained_GAF4 _ _,
    fun a q hq => gafStage_support_GAF4 P.toLocalChartFamily P.zero hΔ hΛ hsmall st a q hq,
    gafStage_fullS_GAF5 P hΔ hΛ hLΛ st,
    gafStage_select_GAF5 P.toLocalChartFamily P.zero hΔ0 st sel hsel⟩

end DifferentialGeometry.Geometry.Collapse
