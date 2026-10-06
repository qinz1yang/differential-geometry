import DifferentialGeometry.Geometry.Fibration.ActualStageFirstPruning
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSegmentLocalization
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageClouds
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageSmallMarkers
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
# Boundary port (lane B-PORT-A): ActualStageFirstPruning (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStageFirstPruning.lean` by
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

/-- The scalar action on a block `ℓ²(ℝ² × ℝ)` is continuous (given directly: the instance search
for it times out). -/
local instance instContinuousSMulPlaneBlock_GAF5_BAUGP : ContinuousSMul ℝ (WithLp 2 (ℝ² × ℝ)) :=
  IsBoundedSMul.continuousSMul

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Generic

section Family

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

open Classical in
/-- CFS27's kept tags at reference radius `r`: every tag except the retained markers `a` with
`ρ(c_a) ≤ r/2`. -/
def firstKeepTags_GAF5_BAUGP (r : ℝ) : Finset (CGPTag_BAUGP L Z) :=
  Finset.univ.filter fun t => ∀ a : CGPMarkerIndex_BAUGP L, cgpMarkerTag_BAUGP L Z a = t →
    r / 2 < ρ (cgpMarkerCentre_BAUGP L a)

open Classical in
/-- The own circle tag of a centre `j` is kept at the reference radius `ρ(j)`. -/
theorem firstKeep_own_GAF5_BAUGP (j : L.circle.finite_centres.toFinset) :
    (.inl j : CGPTag_BAUGP L Z) ∈ firstKeepTags_GAF5_BAUGP L Z (ρ j.1) := by
  rw [firstKeepTags_GAF5_BAUGP, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun a ha => ?_⟩
  have hr := hρ j.1
  rcases a with j' | j' | j'
  · have hj : j' = j := Sum.inl_injective ha
    subst hj
    change ρ j'.1 / 2 < ρ j'.1
    linarith
  · exact absurd ha (by simp [cgpMarkerTag_BAUGP])
  · exact absurd ha (by simp [cgpMarkerTag_BAUGP])

open Classical in
/-- A retained marker with `ρ(c_a) ≤ r/2` is deleted. -/
theorem firstKeep_marker_GAF5_BAUGP {r : ℝ} (a : CGPMarkerIndex_BAUGP L)
    (ha : ρ (cgpMarkerCentre_BAUGP L a) ≤ r / 2) : cgpMarkerTag_BAUGP L Z a ∉
        firstKeepTags_GAF5_BAUGP L Z r := by
  rw [firstKeepTags_GAF5_BAUGP, Finset.mem_filter]
  rintro ⟨-, h⟩
  exact absurd (h a rfl) (not_lt.mpr ha)

open Classical in
/-- The marker of a deleted block vanishes on the range of the pruning. -/
theorem firstPrune_marker_GAF5_BAUGP {r : ℝ} (a : CGPMarkerIndex_BAUGP L)
    (ha : ρ (cgpMarkerCentre_BAUGP L a) ≤ r / 2) (y : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) :
    blockMarkerCLM (cgpMarkerTag_BAUGP L Z a) (blockRestrict (firstKeepTags_GAF5_BAUGP L Z r) y) =
        0 := by
  rw [blockMarkerCLM_apply, blockRestrict_apply, ite_eq_right (firstKeep_marker_GAF5_BAUGP L Z a
      ha)]
  rfl

open Classical in
/-- **The pruning fixes `𝓔⁰` on the chart domain** `B(i, 200ρ(i))` (`Λ·200 ≤ 1/4`): every deleted
block of `𝓔⁰(x)` is zero there. -/
theorem firstPrune_globalMap_GAF5_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4) {i x : X}
    (hx : x ∈ ball i (200 * ρ i)) :
    blockRestrict (firstKeepTags_GAF5_BAUGP L Z (ρ i)) (cgpGlobalMap_BAUGP L Z x) =
        cgpGlobalMap_BAUGP L Z x := by
  refine PiLp.ext fun t => ?_
  rw [blockRestrict_apply]
  split_ifs with ht
  · rfl
  · rw [firstKeepTags_GAF5_BAUGP, Finset.mem_filter] at ht
    push Not at ht
    obtain ⟨a, rfl, ha⟩ := ht (Finset.mem_univ _)
    have hcut : cgpMarkerCutoff_BAUGP L a x = 0 := by
      by_contra hne
      have h1 := cgpMarkerCutoff_scale_lip_GAF4_BAUGP L hΔ hΛ hsmall a x hne
      have h2 := scale_mem_of_dist_lt_KC L.lipschitz_scale hΛ (hρ i) (mem_ball.mp hx) hΛ200
      have hri := hρ i
      linarith [h1.2, h2.1]
    have hb := cgpGlobalMap_markerBlock_GAF2_BAUGP L Z a x
    rw [hcut, mul_zero, zero_smul] at hb
    rw [blockVectorCLM_apply] at hb
    rw [blockMarkerCLM_apply] at hb
    symm
    apply WithLp.ofLp_injective
    exact Prod.ext hb.1 hb.2

open Classical in
/-- **The pruning fixes `d𝓔⁰` on the chart domain** `B(i, 200ρ(i))`. -/
theorem firstPrune_mvfderiv_GAF5_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4) {i x : X}
    (hx : x ∈ ball i (200 * ρ i)) (w : TangentSpace 𝓘(ℝ, E3) x) :
    blockRestrict (firstKeepTags_GAF5_BAUGP L Z (ρ i)) (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP L Z)
        x w) =
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP L Z) x w :=
  clm_mvfderiv_eq_of_eventuallyEq_GAF5 _
    (Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun _ hy =>
      firstPrune_globalMap_GAF5_BAUGP L Z hΔ hΛ hsmall hΛ200 hy) w

end Family

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF5p_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF5p_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF5p_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

end Packets


end DifferentialGeometry.Geometry.Collapse
