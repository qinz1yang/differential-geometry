import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers
import DifferentialGeometry.Geometry.Fibration.ActualStageClouds
import DifferentialGeometry.Geometry.Metric.StageSmallMarkerNear

/-!
# CFS31's `hnear` on the actual stage data

Blueprint `master207B.tex`, CFS28/CFS29 (B:3686–3755) bound to the actual `𝓔⁰` of
`LocalChartPackets`: at every stage `st` with the CFS31 marker data
`v_a = (·)_{tag a}.snd`, `R_a = ρ(c_a)`, `ζ_a = cgpMarkerCutoff`, target `Q_st = gafStageQ st`, a
selection of preimages over `S̃_st`, radii `Σρ(sel x)` with `128 Ξ⁻¹ Σ ≤ 1/5`, planes satisfying the
stage tests' small-marker rule (PP), and a map `p` with CFS24's contributor locality on every core
ball (GAF3's `gaf01_row_nearest_GAF3`), the stage projection `π_{Q_st} ∘ p` has zero small markers
on every core ball (`gafStage_hnear_GAF4`): exactly CFS31's `hnear` for that stage.
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
  {σc μ b s b' s' ε γc βc Lmax τ γ : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNSC_GAF4n
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNSC_GAF4n
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCSC_GAF4n
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- `stage_small_marker_near_GAF4` with a block-space target `H = BlockSpace (fun _ : κ => ℝ²)`,
stated with the instances found on block spaces (matching them with the generic inner-product
statement is done once, here). -/
theorem stage_small_marker_near_block_GAF4 {κ : Type*} [Fintype κ] {A M : Type*}
    (v : A → BlockSpace (fun _ : κ => ℝ²) →L[ℝ] ℝ) (R : A → ℝ) (hR : ∀ a, 0 < R a) (ρ : M → ℝ)
    (hρ : ∀ p, 0 < ρ p) (ζ : A → M → ℝ) (hζ0 : ∀ a p, 0 ≤ ζ a p)
    (F : M → BlockSpace (fun _ : κ => ℝ²)) (hvF : ∀ a p, v a (F p) = R a * ζ a p)
    (Q : Submodule ℝ (BlockSpace (fun _ : κ => ℝ²)))
    (hretained : ∀ a, (LinearMap.ker (v a : BlockSpace (fun _ : κ => ℝ²) →ₗ[ℝ] ℝ))ᗮ ≤ Q ∨
      (LinearMap.ker (v a : BlockSpace (fun _ : κ => ℝ²) →ₗ[ℝ] ℝ))ᗮ ≤ Qᗮ)
    (hsupport : ∀ a q, 0 < v a (Q.starProjection (F q)) →
      3 * R a / 4 ≤ ρ q ∧ ρ q ≤ 5 * R a / 4)
    (S : Set (BlockSpace (fun _ : κ => ℝ²))) (sel : BlockSpace (fun _ : κ => ℝ²) → M)
    (hsel : ∀ x ∈ S, Q.starProjection (F (sel x)) = x)
    (hpre : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x → 3 / 5 * ρ q ≤ ρ (sel x))
    {sg Ξ : ℝ} (hsg : 0 < sg) (hΞ : 0 < Ξ)
    (hmcb : ∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * Ξ⁻¹ * max (sg * ρ (sel y)) (sg * ρ (sel x)) →
      sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel y) ∧ sg * ρ (sel y) ≤ (5 / 3) * (sg * ρ (sel x)))
    (plane : BlockSpace (fun _ : κ => ℝ²) → Submodule ℝ (BlockSpace (fun _ : κ => ℝ²)))
    (hpp : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x → ∀ a, R a < ρ q / 5 →
      plane x ≤ LinearMap.ker (v a : BlockSpace (fun _ : κ => ℝ²) →ₗ[ℝ] ℝ))
    (pn : BlockSpace (fun _ : κ => ℝ²) → BlockSpace (fun _ : κ => ℝ²))
    (hloc : ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)),
      ∀ (K : Submodule ℝ (BlockSpace (fun _ : κ => ℝ²))) (c : BlockSpace (fun _ : κ => ℝ²)),
      (∀ i ∈ S, (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
          ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
        K.starProjection i = c ∧ plane i ≤ Kᗮ) →
      K.starProjection (pn z) = c) :
    ∀ x ∈ S, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q, Q.starProjection (F q) = x →
      ∀ a, R a < ρ q / 16 → v a (Q.starProjection (pn z)) = 0 :=
  stage_small_marker_near_GAF4 v R hR ρ hρ ζ hζ0 F hvF Q hretained hsupport S sel hsel hpre hsg
    hΞ hmcb plane hpp pn hloc

/-- **CFS31's `hnear` at one actual stage.** On `LocalChartPackets` with `1 ≤ Δ`, `0 ≤ Λ`,
`10⁶ΔΛ < 10⁻⁵`: for every stage `st`, selection `sel` of preimages over `S̃_st`, `0 < Σ`, `0 < Ξ`
with `128 Ξ⁻¹ Σ ≤ 1/5`, planes over `S_st` with the small-marker rule (PP) (`plane x ≤ ker v_a`
whenever `ρ(c_a) < ρ(q)/5` for a preimage `q` of `x`), and a map `p` with CFS24's contributor
locality on every `B(x, Σρ(sel x))`: for every `x ∈ S_st`, `z ∈ B(x, Σρ(sel x))`, preimage `q` of
`x` and retained marker `a` with `ρ(c_a) < ρ(q)/16`, the marker `v_a` of `π_{Q_st}(p z)`
vanishes. -/
theorem gafStage_hnear_GAF4
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        (sel x) = x)
    {sg Ξ : ℝ} (hsg : 0 < sg) (hΞ : 0 < Ξ) (hmo : 128 * Ξ⁻¹ * sg ≤ 1 / 5)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hpp : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ q,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st) q =
        x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
        plane x ≤ LinearMap.ker ((blockMarkerCLM
          (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (cgpMarkerTag P.toLocalChartFamily P.zero a) :
            BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ))
    (pn : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hloc : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ∀ (Kk : Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
        (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
          (closedBall i (80 * Ξ⁻¹ * (sg * ρ (sel i))) ∩
            ball x (8 * Ξ⁻¹ * (sg * ρ (sel x)))).Nonempty →
          Kk.starProjection i = c ∧ plane i ≤ Kkᗮ) →
        Kk.starProjection (pn z) = c) :
    ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q,
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
      ∀ a : CGPMarkerIndex P.toLocalChartFamily,
        ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
          ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (pn z)) = 0 := by
  classical
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hSS := gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0.le st
  have hmcb := gafCloud_mcb_GAF2 P.toLocalChartFamily P.zero hΔ hΛ hsmall st sel hsel hsg.le
    (by positivity) hmo
  refine stage_small_marker_near_block_GAF4
    (fun a => blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a))
    (fun a => ρ (cgpMarkerCentre P.toLocalChartFamily a)) (fun a => hρ _) ρ hρ
    (cgpMarkerCutoff P.toLocalChartFamily)
    (fun a p => (cgpMarkerCutoff_mem_Icc_GAF2 P.toLocalChartFamilyQ hΔ0 a p).1)
    (cgpGlobalMap P.toLocalChartFamily P.zero)
    (fun a p => (cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero a p).2)
    (gafStageQ P.toLocalChartFamily P.zero st)
    (fun a => blockMarker_retained_GAF4 _ _)
    (fun a q hq => gafStage_support_GAF4 P.toLocalChartFamily P.zero hΔ hΛ hsmall st a q hq)
    (gafCloud P.toLocalChartFamily P.zero st) sel
    (fun x hx => by
      rw [gafStageQ_starProjection_globalMap]
      exact hsel x (hSS hx))
    (gafCloud_preimage_ratio_GAF4 P.toLocalChartFamily P.zero hΔ hΛ hsmall st sel hsel)
    hsg hΞ (fun x hx y hy hd => hmcb x (hSS hx) y (hSS hy) hd) plane
    (fun x hx q hq a ha => hpp x hx q (by
      rw [← gafStageQ_starProjection_globalMap]
      exact hq) a ha) pn hloc

end DifferentialGeometry.Geometry.Collapse
