import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPacketsApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPlaneCoherence
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphModel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFullMarkerContributors
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSegmentLocalization
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageClouds
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageTargets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualStageSmallMarkers (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStageSmallMarkers.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`); do
not edit by hand, re-run the script. Closed family → boundary family (`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology InnerProductSpace
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Generic

variable {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

variable [Fintype κ] [DecidableEq κ] [∀ i, FiniteDimensional ℝ (V i)]

end Generic

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

/-- (AS) at a positive retained cutoff from slow variation alone:
`3ρ(c_a)/4 ≤ ρ(p) ≤ 5ρ(c_a)/4`. -/
theorem cgpMarkerCutoff_scale_lip_GAF4_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (a : CGPMarkerIndex_BAUGP L) (p : X)
    (hp : cgpMarkerCutoff_BAUGP L a p ≠ 0) :
    3 * ρ (cgpMarkerCentre_BAUGP L a) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (cgpMarkerCentre_BAUGP L a) / 4 := by
  have hΔ0 : 0 < Δ := by linarith
  have hball := cgpMarkerCutoff_ne_zero_BAUGP L hΔ0 a p hp
  rw [mem_ball] at hball
  have hD : cgpMarkerDomain_BAUGP L a ≤ 1000000 * Δ := by
    rcases a with j | j | j
    · change (200 : ℝ) ≤ 1000000 * Δ
      linarith
    · exact le_rfl
    · change 100 * Δ ≤ 1000000 * Δ
      linarith
  have hc0 := hρ (cgpMarkerCentre_BAUGP L a)
  have hlip := L.lipschitz_scale.dist_le_mul p (cgpMarkerCentre_BAUGP L a)
  rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at hlip
  have hd : dist p (cgpMarkerCentre_BAUGP L a) ≤ 1000000 * Δ * ρ (cgpMarkerCentre_BAUGP L a) :=
    hball.le.trans (mul_le_mul_of_nonneg_right hD hc0.le)
  have h1 : Λ * dist p (cgpMarkerCentre_BAUGP L a) ≤ Λ * (1000000 * Δ * ρ (cgpMarkerCentre_BAUGP L
      a)) :=
    mul_le_mul_of_nonneg_left hd hΛ
  have h2 : Λ * (1000000 * Δ * ρ (cgpMarkerCentre_BAUGP L a)) ≤ ρ (cgpMarkerCentre_BAUGP L a) /
      4 := by
    have := mul_le_mul_of_nonneg_right hsmall hc0.le
    nlinarith
  have habs := (abs_le.mp (hlip.trans (h1.trans h2)))
  constructor <;> linarith [habs.1, habs.2]

/-- **Two preimages of a core cloud point** (CFS26): for every selection over `S̃_st`, every
preimage `q` of `x ∈ S_st` has `(3/5)ρ(q) ≤ ρ(sel x)` (stage `0`: equality, from FC04's exact
radius; stages `1, 2`: CFS07 at distance zero). -/
theorem gafCloud_preimage_ratio_GAF4_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged_BAUGP L Z st, cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st)
        (sel x) = x) :
    ∀ x ∈ gafCloud_BAUGP L Z st, ∀ q, (gafStageQ_BAUGP L Z st).starProjection (cgpGlobalMap_BAUGP L
        Z q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) := by
  have hΔ0 : 0 ≤ Δ := by linarith
  intro x hx q hq
  rw [gafStageQ_starProjection_globalMap_BAUGP] at hq
  have hxe := gafCloud_subset_enlarged_BAUGP L Z hΔ0 st hx
  have hsx := hsel x hxe
  fin_cases st
  · have huniv := cgpProjMap_univ_GAF_BAUGP L Z
    have hq' : cgpGlobalMap_BAUGP L Z q = x := by
      rw [← huniv]
      exact hq
    have hs' : cgpGlobalMap_BAUGP L Z (sel x) = x := by
      rw [← huniv]
      exact hsx
    have hr := (fc04_first_cloud_scale_BAUGP L Z (L' := 0) (sg := 1) zero_le_one (by norm_num)).1
    have h1 := hr q
    have h2 := hr (sel x)
    rw [hq'] at h1
    rw [hs'] at h2
    have heq : ρ q = ρ (sel x) := by linarith
    have := hρ q
    rw [← heq]
    linarith
  · have hx8 : x ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) '' fc27EdgeSet_BAUGP L 8 := hxe
    have hmc := (fc27_edge_cloud_scale_BAUGP L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) q = x from hq,
          show cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) (sel x) = x from hsx, dist_self]
        simp)
    exact hmc.1
  · have hx8 : x ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) '' fc27SlimSet_BAUGP L 8 := hxe
    have hmc := (fc27_slim_cloud_scale_BAUGP L Z hΔ hΛ hsmall).2.2.2 0 0 le_rfl le_rfl (by norm_num)
      q (sel x) (by rw [show cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) q = x from hq]; exact hx8)
      (by rw [show cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) (sel x) = x from hsx]; exact hx8)
      (by
        rw [show cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) q = x from hq,
          show cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) (sel x) = x from hsx, dist_self]
        simp)
    exact hmc.1


end DifferentialGeometry.Geometry.Collapse
