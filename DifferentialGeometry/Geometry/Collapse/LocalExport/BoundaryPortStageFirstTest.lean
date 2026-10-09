import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTest
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCircleGram
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPacketsApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPlaneCoherence
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstCloudCoverage
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphAssembly
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphData
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphEdgeGroup
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTags
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTagsScalar
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFullMarkerContributors
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortHeightComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageClouds
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageTargets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeetingTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroRawTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroAdaptedPhysicalTest
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualStageFirstTest (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStageFirstTest.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
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

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

/-- The first stage cloud is the `𝓔⁰`-image of FC04's core (`π₁ = id`). -/
theorem gafCloud_zero_GAF4_BAUGP : gafCloud_BAUGP L Z 0 = cgpGlobalMap_BAUGP L Z '' fc04Set_BAUGP L
    Z 7 := by
  change cgpProjMap_BAUGP L Z Finset.univ '' fc04Set_BAUGP L Z 7 = _
  rw [cgpProjMap_univ_GAF_BAUGP]

/-- The enlarged first stage cloud is the `𝓔⁰`-image of FC04's enlargement. -/
theorem gafCloudEnlarged_zero_GAF4_BAUGP :
    gafCloudEnlarged_BAUGP L Z 0 = cgpGlobalMap_BAUGP L Z '' fc04Set_BAUGP L Z 8 := by
  change cgpProjMap_BAUGP L Z Finset.univ '' fc04Set_BAUGP L Z 8 = _
  rw [cgpProjMap_univ_GAF_BAUGP]

/-- The first stage target is the whole block space. -/
theorem gafStageQ_zero_GAF4_BAUGP : gafStageQ_BAUGP L Z 0 = ⊤ := by
  classical
  rw [eq_top_iff]
  intro v _
  rw [mem_gafStageQ_iff_BAUGP]
  change blockRestrict Finset.univ v = v
  rw [blockRestrict_univ]
  rfl

/-- **TCP06's clauses in the stage form.** Dimension `2` and the (CS) test at FC04's exact radius
`scaleRadius Σ` over `S₁ = 𝓔⁰(A₁)` give, at stage `0`: dimension `gafStageDim 0`, planes inside
`gafStageQ_BAUGP 0`, and the (CS) test at radius `Σρ(sel x)` for every selection of preimages over
`S̃₁`. -/
theorem fc27_first_of_tcp06_GAF4_BAUGP
    (plane : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))) {sg Γ : ℝ} (hsg : 0 ≤ sg)
    (hdim : ∀ x ∈ cgpGlobalMap_BAUGP L Z '' fc04Set_BAUGP L Z 7, Module.finrank ℝ (plane x) = 2)
    (hcs : ∀ x ∈ cgpGlobalMap_BAUGP L Z '' fc04Set_BAUGP L Z 7,
      hausdorffEDist (cgpGlobalMap_BAUGP L Z '' fc04Set_BAUGP L Z 8 ∩
          ball x (scaleRadius (cgpScaleTag_BAUGP L Z) sg x / Γ))
        ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag_BAUGP L Z) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag_BAUGP L Z) sg x)) :
    (∀ x ∈ gafCloud_BAUGP L Z 0, Module.finrank ℝ (plane x) = gafStageDim 0 ∧
      plane x ≤ gafStageQ_BAUGP L Z 0) ∧
    ∀ sel : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) → X,
      (∀ x ∈ gafCloudEnlarged_BAUGP L Z 0, cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z 0) (sel
          x) = x) →
      ∀ x ∈ gafCloud_BAUGP L Z 0,
        hausdorffEDist (gafCloudEnlarged_BAUGP L Z 0 ∩ ball x (sg * ρ (sel x) / Γ))
          ((AffineSubspace.mk' x (plane x) : Set (BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))) ∩
            ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x))) := by
  rw [gafCloud_zero_GAF4_BAUGP, gafStageQ_zero_GAF4_BAUGP]
  refine ⟨fun x hx => ⟨hdim x hx, le_top⟩, fun sel hsel x hx => ?_⟩
  rw [gafCloudEnlarged_zero_GAF4_BAUGP] at hsel ⊢
  have hx8 : x ∈ cgpGlobalMap_BAUGP L Z '' fc04Set_BAUGP L Z 8 :=
    image_mono (fc04Set_mono_BAUGP L Z (by norm_num)) hx
  have hF : cgpGlobalMap_BAUGP L Z (sel x) = x := by
    rw [← cgpProjMap_univ_GAF_BAUGP L Z]
    exact hsel x hx8
  have hr : scaleRadius (cgpScaleTag_BAUGP L Z) sg x = sg * ρ (sel x) := by
    have h0 := (fc04_first_cloud_scale_BAUGP L Z (L' := 0) hsg (by norm_num)).1 (sel x)
    rw [hF] at h0
    exact h0
  have h := hcs x hx
  rw [hr] at h
  exact h

end Model

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_GAF4f_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF4f_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF4f_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a


end DifferentialGeometry.Geometry.Collapse
