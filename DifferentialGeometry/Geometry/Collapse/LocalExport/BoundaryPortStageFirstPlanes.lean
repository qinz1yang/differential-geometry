import DifferentialGeometry.Geometry.Fibration.ActualStageFirstPlanes
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTable
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTags
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFirstGraphTagsScalar
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortFullMarkerContributors
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortHeightComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortModelMarkerPlanes
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSegmentLocalization
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageClouds
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageFirstPruning
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageFirstTest
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStagePlaneTypes
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
# Boundary port (lane B-PORT-A): ActualStageFirstPlanes (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStageFirstPlanes.lean` by
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


/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_PLNf_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNf_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNf_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

open Classical in
/-- **TCP05 with CFS27's pruning on an EXPLICIT model** (`tcp05_pruned_scale_GAF5` without the
existential: the pruned model is `K_j ∘ Φ`, `K_j = π_{keep(ρ(j))}`). For `Φ` smooth with own block
`(a, 1)` at `j`, `‖DΦ‖, ‖D²Φ‖ ≤ C`, (TG) on `B(j, 200ρ(j)) ∩ {‖η_j‖ ≤ 8}` and zero scale
derivative: `K_j ∘ Φ` is smooth, has the own block, the same bounds and (TG) (`tcpTG_PLN_BAUGP`),
its
derivative is annihilated by the marker of every block with `ρ(c_a) ≤ ρ(j)/2`, and its scale
derivative is zero. -/
theorem tcp05_pruned_explicit_PLN_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4)
    {eg : ℝ} (j : P.toLocalPacketsOnB.circle.finite_centres.toFinset)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))
    (hsm : ContDiff ℝ ∞ Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1))
    (hb : ∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst)
    (hTG : tcpTG_PLN_BAUGP P eg Φ
      (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 ((Set.Finite.mem_toFinset _).mp j.2)) j.1)
    (hscale : ∀ a h, fderiv ℝ Φ a h (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) = 0) :
    ContDiff ℝ ∞ (blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ j.1)) ∘ Φ) ∧
    (∀ a, (blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ j.1)) ∘ Φ) a (.inl
        j) =
      WithLp.toLp 2 (a, 1)) ∧
    (∀ a, ‖fderiv ℝ (blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ j.1)) ∘
        Φ)
        a‖ ≤ tcpGraphConst ∧
      ‖fderiv ℝ (fderiv ℝ (blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero
        (ρ j.1)) ∘ Φ)) a‖ ≤ tcpGraphConst) ∧
    tcpTG_PLN_BAUGP P eg (blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ
        j.1)) ∘ Φ)
      (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 ((Set.Finite.mem_toFinset _).mp j.2)) j.1 ∧
    (∀ a : CGPMarkerIndex_BAUGP P.toLocalPacketsOnB,
      ρ (cgpMarkerCentre_BAUGP P.toLocalPacketsOnB a) ≤ ρ j.1 / 2 → ∀ u v,
      blockMarkerCLM (cgpMarkerTag_BAUGP P.toLocalPacketsOnB P.zero a)
        (fderiv ℝ (blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ j.1)) ∘ Φ)
          u v) = 0) ∧
    ∀ u v, blockMarkerCLM (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero)
      (fderiv ℝ (blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ j.1)) ∘ Φ)
        u v) = 0 := by
  have hsm2 : ContDiff ℝ 2 Φ := hsm.of_le (by simp)
  have hd : Differentiable ℝ Φ := hsm.differentiable (by simp)
  set Kp := blockRestrict (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)
    (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ j.1)) with hKp
  set η := cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 ((Set.Finite.mem_toFinset _).mp j.2) with hη
  have hD : ∀ u, fderiv ℝ (Kp ∘ Φ) u = Kp.comp (fderiv ℝ Φ u) := fun u => by
    rw [fderiv_comp u Kp.differentiableAt (hd u), Kp.fderiv]
  refine ⟨Kp.contDiff.comp hsm, fun a => ?_,
    fun a => clm_comp_bounds_GAF5 Kp (norm_blockRestrict_le _) hsm2 (fun y => (hb y).1)
      (fun y => (hb y).2) a, fun x hx hx8 => ⟨?_, fun w => ?_⟩, fun a ha u v => ?_,
    fun u v => ?_⟩
  · change Kp (Φ a) (.inl j) = _
    rw [hKp, blockRestrict_apply, ite_eq_left (firstKeep_own_GAF5_BAUGP P.toLocalPacketsOnB P.zero
        j)]
    exact hown a
  · have hfix := firstPrune_globalMap_GAF5_BAUGP P.toLocalPacketsOnB P.zero hΔ hΛ hsmall hΛ200 hx
    have h1 : (ρ j.1)⁻¹ • cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero x - (Kp ∘ Φ) (η x) =
        Kp ((ρ j.1)⁻¹ • cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero x - Φ (η x)) := by
      rw [map_sub, map_smul]
      change _ = (ρ j.1)⁻¹ • Kp (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero x) - _
      rw [hKp, hfix]
      rfl
    rw [h1]
    exact lt_of_le_of_lt (norm_blockRestrict_apply_le _ _) (hTG x hx hx8).1
  · have hfix := firstPrune_mvfderiv_GAF5_BAUGP P.toLocalPacketsOnB P.zero hΔ hΛ hsmall hΛ200 hx w
    have h1 : (ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero) x w -
        fderiv ℝ (Kp ∘ Φ) (η x) (mvfderiv 𝓘(ℝ, E3) η x w) =
        Kp ((ρ j.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero) x w -
          fderiv ℝ Φ (η x) (mvfderiv 𝓘(ℝ, E3) η x w)) := by
      rw [hD, map_sub, map_smul]
      change _ = (ρ j.1)⁻¹ • Kp (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero)
          x w) -
        _
      rw [hKp, hfix]
      rfl
    rw [h1]
    exact (norm_blockRestrict_apply_le _ _).trans ((hTG x hx hx8).2 w)
  · rw [hD]
    exact firstPrune_marker_GAF5_BAUGP P.toLocalPacketsOnB P.zero a ha _
  · rw [hD]
    change blockMarkerCLM _ (Kp (fderiv ℝ Φ u v)) = 0
    rw [hKp, blockMarkerCLM_apply, blockRestrict_apply]
    split_ifs
    · rw [hscale u v]
      rfl
    · rfl

/-- **TCP06 at one circle centre, with (PP), plane named** (`tcp06_centre_pps_GAF5` with the
witness `W = im DΦ(η_j p)` explicit and the rank in the units of `j` itself,
`tcpNormalSpec_PLN_BAUGP`):
for a model `Φ` with own block, `C²` bounds, (TG), pruned small markers and zero scale derivative,
and a core witness `p` of `j` with `x = 𝓔⁰(p)`: `dim W = 2`, the (CS) test at FC04's radius, the
rank clauses at every preimage, `W ≤ ker v_scale`, and (PP). -/
theorem tcp06_explicit_point_PLN_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hΛ200 : Λ * 200 ≤ 1 / 4) (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) (j : P.toLocalPacketsOnB.circle.finite_centres.toFinset)
    (Φ : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))
    (hsm : ContDiff ℝ ∞ Φ) (hown : ∀ a, Φ a (.inl j) = WithLp.toLp 2 (a, 1))
    (hb : ∀ a, ‖fderiv ℝ Φ a‖ ≤ tcpGraphConst ∧ ‖fderiv ℝ (fderiv ℝ Φ) a‖ ≤ tcpGraphConst)
    (hTG : tcpTG_PLN_BAUGP P eg Φ
      (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 ((Set.Finite.mem_toFinset _).mp j.2)) j.1)
    (hprune : ∀ a : CGPMarkerIndex_BAUGP P.toLocalPacketsOnB,
      ρ (cgpMarkerCentre_BAUGP P.toLocalPacketsOnB a) ≤ ρ j.1 / 2 → ∀ u v,
      blockMarkerCLM (cgpMarkerTag_BAUGP P.toLocalPacketsOnB P.zero a) (fderiv ℝ Φ u v) = 0)
    (hscale : ∀ u v,
      blockMarkerCLM (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) (fderiv ℝ Φ u v) = 0)
    {p : X} (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hηp : ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 ((Set.Finite.mem_toFinset _).mp j.2) p‖ ≤
      7) {x : BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)}
    (hpx : cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero p = x) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ Φ (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1
        ((Set.Finite.mem_toFinset _).mp j.2) p) : ℝ² →ₗ[ℝ]
            BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))) = 2 ∧
      hausdorffEDist (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero ''
          fc04Set_BAUGP P.toLocalPacketsOnB P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) sg x / Γ))
        ((AffineSubspace.mk' x (LinearMap.range (fderiv ℝ Φ (cgpCircleCoord_BAUGP
            P.toLocalPacketsOnB
          j.1 ((Set.Finite.mem_toFinset _).mp j.2) p) : ℝ² →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))) :
            Set (BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) sg x) ∧
      (∀ q, cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero q = x →
        tcpNormalSpec_PLN_BAUGP P eg (LinearMap.range (fderiv ℝ Φ (cgpCircleCoord_BAUGP
            P.toLocalPacketsOnB
          j.1 ((Set.Finite.mem_toFinset _).mp j.2) p) : ℝ² →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))) j.1 q) ∧
      LinearMap.range (fderiv ℝ Φ (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1
          ((Set.Finite.mem_toFinset _).mp j.2) p) : ℝ² →ₗ[ℝ]
              BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)) ≤
        LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)
          (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) :
              BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →ₗ[ℝ] ℝ) ∧
      ∀ q, cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero q = x →
        ∀ a : CGPMarkerIndex_BAUGP P.toLocalPacketsOnB,
          ρ (cgpMarkerCentre_BAUGP P.toLocalPacketsOnB a) < ρ q / 5 →
          LinearMap.range (fderiv ℝ Φ (cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1
              ((Set.Finite.mem_toFinset _).mp j.2) p) : ℝ² →ₗ[ℝ]
                  BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)) ≤
            LinearMap.ker ((blockMarkerCLM (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero =>
                ℝ²)
              (cgpMarkerTag_BAUGP P.toLocalPacketsOnB P.zero a) :
                  BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →L[ℝ] ℝ) :
              BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  subst hpx
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hC : 0 < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
  have hsm2 : ContDiff ℝ 2 Φ := hsm.of_le (by simp)
  have hpoint := tcp06_point_KA8_BAUGP P.toLocalPacketsOnB hΛ hΛ200 hj j rfl Φ hsm2 hown
    (fun a => (hb a).2) hΓ hΓ1 hsg hsgΓ hC hsgC heg hegΓ (fun y hy hyη => (hTG y hy hyη).1) hp hηp
  refine ⟨hpoint.1, hpoint.2, fun q hq => ?_, ?_, fun q hq a ha => ?_⟩
  · exact tcp06_rank_point_KA8_BAUGP P.toLocalPacketsOnB hβ hγβ hj j rfl Φ hsm2 hown
      (fun a => (hb a).1) heg1 (fun y hy hyη => (hTG y hy hyη).2) hp hηp hq
  · intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
    rw [LinearMap.mem_ker]
    exact hscale _ u
  have hfm := tcp06_full_marker_KA8_BAUGP P.toLocalPacketsOnB hj j rfl hp
    (le_trans hηp (by norm_num)) hq
  have hsc := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ j.1) (mem_ball.mp hfm.1) hΛ200
  have hrj := hρ j.1
  have hsa : ρ (cgpMarkerCentre_BAUGP P.toLocalPacketsOnB a) ≤ ρ j.1 / 2 := by linarith [hsc.2]
  intro w hw
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
  rw [LinearMap.mem_ker]
  exact hprune a hsa _ u

open Classical in
/-- **The stage-`0` witness from TCP05's table**: with TCP06's numbers (`Λ·200 ≤ 1/4`,
`β₂ ≤ 10⁻⁷`, `γ + β₂ ≤ 1/10`), (TP) and TCP05's table at every circle centre (the conclusion of
`tcp05_row_table_PLN_BAUGP`), the enhanced stage-`0` plane witness exists. -/
theorem firstStagePlanes_of_table_PLN_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (hΛ200 : Λ * 200 ≤ 1 / 4)
    (hβ : β 2 ≤ 1 / 10000000) (hγβ : γ + β 2 ≤ 1 / 10)
    {Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100)
    (hTab :
    ∀ i (hi : i ∈ P.circle.centres),
      ∃ (Ac : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ² →L[ℝ] ℝ²)
        (cc : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ²)
        (A1 : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ² →L[ℝ] ℝ)
        (c1 : CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ) (Bτ : ℝ² →L[ℝ] ℝ) (cτ : ℝ),
        (∀ a, ‖fderiv ℝ (tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero i
              (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero i) (tcpListedEdges_BAUGP
                  P.toLocalPacketsOnB i)
              Ac cc A1 c1 Bτ cτ) a‖ ≤ tcpGraphConst ∧
          ‖fderiv ℝ (fderiv ℝ (tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero i
              (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero i) (tcpListedEdges_BAUGP
                  P.toLocalPacketsOnB i)
              Ac cc A1 c1 Bτ cτ)) a‖ ≤ tcpGraphConst) ∧
        ∀ x ∈ ball i (200 * ρ i), ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x‖ ≤ 8 →
          ‖(ρ i)⁻¹ • cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero x -
              (tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero i
              (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero i) (tcpListedEdges_BAUGP
                  P.toLocalPacketsOnB i)
              Ac cc A1 c1 Bτ cτ) (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x)‖ < eg ∧
          ∀ w : TangentSpace 𝓘(ℝ, E3) x,
            ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero) x w -
                fderiv ℝ (tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero i
              (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero i) (tcpListedEdges_BAUGP
                  P.toLocalPacketsOnB i)
              Ac cc A1 c1 Bτ cτ) (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi x)
                  (mvfderiv 𝓘(ℝ, E3) (cgpCircleCoord_BAUGP P.toLocalPacketsOnB i hi) x w)‖ ≤
              eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w)) :
    Nonempty (FirstStagePlanes_PLN_BAUGP P Γ sg eg) := by
  have hm : ∀ a : P.toLocalPacketsOnB.circle.finite_centres.toFinset, a.1 ∈ P.circle.centres :=
    fun a => (Set.Finite.mem_toFinset _).mp a.2
  choose Acf ccf A1f c1f Bτf cτf hspec using hTab
  have hC : 0 < tcpGraphConst := lt_of_lt_of_le one_pos one_le_tcpGraphConst
  -- the model table and its pruning at every reference
  obtain ⟨model, hmodel⟩ : ∃ model : P.toLocalPacketsOnB.circle.finite_centres.toFinset → ℝ² →
      BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²),
          ∀ a, model a = tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero a.1
        (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero a.1) (tcpListedEdges_BAUGP
            P.toLocalPacketsOnB a.1)
        (Acf a.1 (hm a)) (ccf a.1 (hm a)) (A1f a.1 (hm a)) (c1f a.1 (hm a)) (Bτf a.1 (hm a))
        (cτf a.1 (hm a)) :=
    ⟨fun a => tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero a.1
        (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero a.1) (tcpListedEdges_BAUGP
            P.toLocalPacketsOnB a.1)
        (Acf a.1 (hm a)) (ccf a.1 (hm a)) (A1f a.1 (hm a)) (c1f a.1 (hm a)) (Bτf a.1 (hm a))
        (cτf a.1 (hm a)), fun a => rfl⟩
  have hpr := fun a : P.toLocalPacketsOnB.circle.finite_centres.toFinset =>
    tcp05_pruned_explicit_PLN_BAUGP P hΔ hΛ hsmall hΛ200 a (model a)
      (by rw [hmodel a]; exact contDiff_tcpModelGraph_BAUGP _ _ _ _ _ _ _ _ _ _ _)
      (fun u => by rw [hmodel a]; exact tcpModelGraph_own_BAUGP _ _ _ _ _ _ _ _ _ _ _ a rfl u)
      (by rw [hmodel a]; exact (hspec a.1 (hm a)).1)
      (by rw [hmodel a]; exact (hspec a.1 (hm a)).2)
      (fun u h => by
        rw [hmodel a]
        exact tcpModelGraph_scale_fderiv_GAFS_BAUGP _ _ _ _ _ _ _ _ _ _ _ u h)
  -- the model preimages and references over `S₁`
  have hpt : ∀ x : gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0,
      ∃ (p : X) (j : P.toLocalPacketsOnB.circle.finite_centres.toFinset),
        p ∈ ball j.1 (200 * ρ j.1) ∧ ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB j.1 (hm j) p‖ ≤ 7 ∧
        cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero
            0) p =
          x.1 := by
    intro x
    obtain ⟨p, hp, hpx⟩ := x.2
    have hp' : p ∈ fc04Set_BAUGP P.toLocalPacketsOnB P.zero 7 := hp
    obtain ⟨j, hpj, hηj⟩ := hp'
    exact ⟨p, j, hpj, hηj, hpx⟩
  choose pre ref hpre using hpt
  have hrp : ∀ x : gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0, ∃ q : X,
      q ∈ gafStageEnlargement_BAUGP P.toLocalPacketsOnB P.zero 0 ∧
        cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero
            0) q =
          x.1 := fun x => x.2
  choose rpre hrpre using hrp
  obtain ⟨D, hDr, hDp, hDref, hDm, hDk, hDc⟩ : ∃ D : StagePlaneData_PLN X (BlockSpace
      (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)) ℝ²
      P.toLocalPacketsOnB.circle.finite_centres.toFinset (gafCloud_BAUGP P.toLocalPacketsOnB P.zero
          0)
      (gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0),
      D.rpre = rpre ∧ D.pre = pre ∧ D.ref = ref ∧ D.model = model ∧
      D.prune = (fun a => blockRestrict (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)
        (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ a.1))) ∧
      D.coord = (fun a => cgpCircleCoord_BAUGP P.toLocalPacketsOnB a.1 (hm a)) :=
    ⟨⟨rpre, pre, ref, model, _, _⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hDpl : ∀ x (hx : x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0),
      D.plane x = LinearMap.range (fderiv ℝ
        (blockRestrict (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)
          (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ (ref ⟨x, hx⟩).1)) ∘
          model (ref ⟨x, hx⟩))
        (cgpCircleCoord_BAUGP P.toLocalPacketsOnB (ref ⟨x, hx⟩).1 (hm (ref ⟨x, hx⟩)) (pre ⟨x, hx⟩))
            :
          ℝ² →ₗ[ℝ] BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)) := fun x hx
              => by
    rw [D.plane_of_mem hx, hDk, hDm, hDc, hDref, hDp]
  -- the witness point of a cloud point
  have hFx : ∀ x (hx : x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0),
      cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero (pre ⟨x, hx⟩) = x := fun x hx => by
    rw [← cgpProjMap_univ_GAF_BAUGP P.toLocalPacketsOnB P.zero]
    exact (hpre ⟨x, hx⟩).2.2
  have hpoint := fun x (hx : x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0) =>
    tcp06_explicit_point_PLN_BAUGP P hΛ hΛ200 hβ hγβ hΓ hΓ1 hsg hsgΓ hsgC heg heg1
      hegΓ (ref ⟨x, hx⟩) _ (hpr (ref ⟨x, hx⟩)).1 (hpr (ref ⟨x, hx⟩)).2.1
      (hpr (ref ⟨x, hx⟩)).2.2.1 (hpr (ref ⟨x, hx⟩)).2.2.2.1 (hpr (ref ⟨x, hx⟩)).2.2.2.2.1
      (hpr (ref ⟨x, hx⟩)).2.2.2.2.2 (hpre ⟨x, hx⟩).1 (hpre ⟨x, hx⟩).2.1 (hFx x hx)
  have hdim : ∀ x ∈ cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero '' fc04Set_BAUGP
      P.toLocalPacketsOnB P.zero
      7,
      Module.finrank ℝ (D.plane x) = 2 := by
    intro x hx
    have hxS : x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0 := by
      rw [gafCloud_zero_GAF4_BAUGP]
      exact hx
    rw [hDpl x hxS]
    exact (hpoint x hxS).1
  have hcs : ∀ x ∈ cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero '' fc04Set_BAUGP
      P.toLocalPacketsOnB P.zero
      7,
      hausdorffEDist (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero ''
          fc04Set_BAUGP P.toLocalPacketsOnB P.zero 8 ∩
          ball x (scaleRadius (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) sg x / Γ))
        ((AffineSubspace.mk' x (D.plane x) : Set (BlockSpace
            (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))) ∩
          ball x (scaleRadius (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) sg x / Γ)) ≤
        ENNReal.ofReal (Γ * scaleRadius (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) sg x) := by
    intro x hx
    have hxS : x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0 := by
      rw [gafCloud_zero_GAF4_BAUGP]
      exact hx
    rw [hDpl x hxS]
    exact (hpoint x hxS).2.1
  have hconv := fc27_first_of_tcp06_GAF4_BAUGP P.toLocalPacketsOnB P.zero D.plane hsg.le hdim hcs
  refine ⟨{ toStagePlaneData_PLN := D
            Ac := fun a => Acf a.1 (hm a)
            cc := fun a => ccf a.1 (hm a)
            A1 := fun a => A1f a.1 (hm a)
            c1 := fun a => c1f a.1 (hm a)
            Bτ := fun a => Bτf a.1 (hm a)
            cτ := fun a => cτf a.1 (hm a)
            model_eq := fun a => by rw [hDm]; exact hmodel a
            prune_eq := fun a => by rw [hDk]
            coord_eq := fun a => by rw [hDc]
            model_bounds := fun a => by rw [hDk, hDm]; exact (hpr a).2.2.1
            model_tg := fun a => by rw [hDk, hDm, hDc]; exact (hpr a).2.2.2.1
            rpre_spec := fun x => by rw [hDr]; exact hrpre x
            pre_spec := fun x => by rw [hDp, hDref, hDc]; exact hpre x
            dimension := hconv.1
            cloudy := hconv.2
            normal := fun x hx q hq => ?_
            scale_zero := fun x hx => ?_
            small_pp := fun x hx q hq a ha => ?_ }⟩
  · -- TCP06's rank at every preimage
    change tcpNormalSpec_PLN_BAUGP P eg (D.plane x) (D.ref ⟨x, hx⟩).1 q
    rw [hDpl x hx, hDref]
    exact (hpoint x hx).2.2.1 q hq
  · -- EDP01's scale clause
    change D.plane x ≤ _
    rw [hDpl x hx]
    exact (hpoint x hx).2.2.2.1
  · -- (PP)
    have hq' : cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero q = x := by
      rw [← cgpProjMap_univ_GAF_BAUGP P.toLocalPacketsOnB P.zero]
      exact hq
    change D.plane x ≤ _
    rw [hDpl x hx]
    exact (hpoint x hx).2.2.2.2 q hq' a ha


/-- **The enhanced stage-`0` plane witness exists** (FC27 first cloud with TCP05's table, review
60's TCP05 / TCP06 / FC27 packages): for (TP) `0 < Γ < 1`, `0 < Σ < min(Γ/200, Γ³/(100C))`,
`0 < e < min(1/100, ΓΣ/100)` and the exclusion quality `ν` there are the thresholds of
`fc27_first_test_pps_GAF5` (verbatim, `Δ ≥ 1200`) such that every actual `LocalChartPacketsC14`
satisfying them carries a `FirstStagePlanes_PLN_BAUGP P Γ Σ e`. -/
theorem exists_firstStagePlanes_PLN_BAUGP {ν Γ sg eg : ℝ} (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg)
    (hsgΓ : sg < Γ / 200) (hsgC : sg < Γ ^ 3 / (100 * tcpGraphConst)) (heg : 0 < eg)
    (heg1 : eg < 1 / 100) (hegΓ : eg < Γ * sg / 100) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ γ₀ ηc θ : ℝ, 0 < η₂ ∧ 0 < γ₀ ∧ 0 < ηc ∧ 0 < θ ∧
    θ < 1 ∧ ∀ Δ : ℝ, 1200 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
          vs ζ Λz U₁ U₂ Ue₁ Ue₂),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      0 ≤ ε → ε ≤ 1 → 0 ≤ σc → σc ≤ θ ^ 2 / 1000 → μ * Δ ≤ θ / 100 →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → γ ≤ γ₀ → 0 < γc → γc ≤ γ₀ → βc ≤ ηc →
      b ≤ η₁ → β 1 ≤ η₁ → 0 < σs → σs ≤ θ ^ 2 / 1000 → vs ≤ θ / 100 → 0 < ζ →
      ζ ≤ θ ^ 2 / 1000 → εr ≤ θ / 100 → 20 * Λz ≤ T → σ⁻¹ ≤ Lmax →
      1000 * tcpGraphConst * Δ * Λ < eg →
      Nonempty (FirstStagePlanes_PLN_BAUGP P Γ sg eg) := by
  obtain ⟨σ, hσ, hσ1, η₂, γ₀, ηc, θ, hη₂, hγ₀, hηc, hθ, hθ1, hrow⟩ :=
    tcp05_row_table_PLN_BAUGP heg heg1 hν hν1
  refine ⟨σ, hσ, hσ1, min η₂ (1 / 10000000), min γ₀ (1 / 20), ηc, θ, lt_min hη₂ (by norm_num),
    lt_min hγ₀ (by norm_num), hηc, hθ, hθ1, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, h⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz U₁
      U₂ Ue₁ Ue₂ P
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25
    h26 h27 h28 h29 h30 h31
  have hTCP := h P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    (h16.trans (min_le_left _ _)) (h17.trans (min_le_left _ _)) h18
    (h19.trans (min_le_left _ _)) h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  have hnum := tcp06_numbers_KA8 hΔ h1 h4 (h17.trans (min_le_right _ _))
    (h16.trans (min_le_right _ _))
  have hΔ1 : 1 ≤ Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  exact firstStagePlanes_of_table_PLN_BAUGP P hΔ1 h1 hsmall hnum.1 (h16.trans (min_le_right _ _))
      hnum.2
    hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ hTCP

end C14


end DifferentialGeometry.Geometry.Collapse
