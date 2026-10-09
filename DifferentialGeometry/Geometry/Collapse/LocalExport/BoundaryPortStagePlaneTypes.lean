import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneTypes
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortModelMarkerPlanes
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSegmentLocalization
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSlimDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageClouds
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageFirstPruning
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageFirstTest
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
# Boundary port (lane B-PORT-A): ActualStagePlaneTypes (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStagePlaneTypes.lean` by
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
local instance instMetricNC14_PLNt_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNt_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNt_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- TCP05's graph comparison (TG) of a model `Ψ` in a chart `η` of the circle centre `c`, on the
reference core `B(c, 200ρ(c)) ∩ {‖η‖ ≤ 8}`: value error `< e`, derivative error `≤ e|w|` (`|w|` of
`ρ(c)⁻²g`). -/
def tcpTG_PLN_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (eg : ℝ)
    (Ψ : ℝ² → BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)) (η : X → ℝ²)
    (c : X) : Prop :=
  ∀ x ∈ ball c (200 * ρ c), ‖η x‖ ≤ 8 →
    ‖(ρ c)⁻¹ • cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero x - Ψ (η x)‖ < eg ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) x,
      ‖(ρ c)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero) x w -
          fderiv ℝ Ψ (η x) (mvfderiv 𝓘(ℝ, E3) η x w)‖ ≤
        eg * Real.sqrt ((ρ c)⁻¹ ^ 2 * g.inner x w w)

/-- TCP06's rank / normal clauses for a plane `W` at a preimage `q`, in the units of `ρ(i)`
(`P_q = π_W ∘ ρ(i)⁻¹d𝓔⁰_q`: onto, normal error `≤ e`, lower bound `1/2` on `ker P_q`ᗮ, upper bound
`3C`). -/
def tcpNormalSpec_PLN_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (eg : ℝ)
    (W : Submodule ℝ (BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))) (i q :
        X) :
    Prop :=
  let Pq := W.orthogonalProjectionOnto.comp
    ((ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero) q)
  Function.Surjective Pq ∧
  (∀ v, ‖(ρ i)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero) q v -
      (Pq v : BlockSpace _)‖ ≤ eg * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v)) ∧
  (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
    1 / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
  ∀ v, ‖Pq v‖ ≤ 3 * tcpGraphConst * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q v v)

open Classical in
/-- **Stage `0` (circle / TCP05–TCP06, `Q₁ = H`, planes of dimension `2`)**: the enhanced plane
witness. Its reference-model table is TCP05's joint output on the SAME `Φ_a` (review 60):
global `C²` bounds, own block, (TG), and — from the model equation and the pruning equation —
frozen scale and CFS27's pruning. -/
structure FirstStagePlanes_PLN_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (Γ sg eg : ℝ) extends
    StagePlaneData_PLN X (BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)) ℝ²
      P.toLocalPacketsOnB.circle.finite_centres.toFinset (gafCloud_BAUGP P.toLocalPacketsOnB P.zero
          0)
      (gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0) where
  /-- TCP05's circle rows `A_j` at every reference. -/
  Ac : P.toLocalPacketsOnB.circle.finite_centres.toFinset →
    CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ² →L[ℝ] ℝ²
  /-- TCP05's circle offsets `c_j` at every reference. -/
  cc : P.toLocalPacketsOnB.circle.finite_centres.toFinset → CGPTag_BAUGP P.toLocalPacketsOnB P.zero
      → ℝ²
  /-- TCP05's scalar rows (slim, edge, zero) at every reference. -/
  A1 : P.toLocalPacketsOnB.circle.finite_centres.toFinset →
    CGPTag_BAUGP P.toLocalPacketsOnB P.zero → ℝ² →L[ℝ] ℝ
  /-- TCP05's scalar offsets at every reference. -/
  c1 : P.toLocalPacketsOnB.circle.finite_centres.toFinset → CGPTag_BAUGP P.toLocalPacketsOnB P.zero
      → ℝ
  /-- TCP05's height row at every reference. -/
  Bτ : P.toLocalPacketsOnB.circle.finite_centres.toFinset → ℝ² →L[ℝ] ℝ
  /-- TCP05's height offset at every reference. -/
  cτ : P.toLocalPacketsOnB.circle.finite_centres.toFinset → ℝ
  /-- The actual model: TCP05's model graph with the ACTUAL support lists of
  `D_a = B(a, 10ρ(a))`. -/
  model_eq : ∀ a, model a = tcpModelGraph_BAUGP P.toLocalPacketsOnB P.zero a.1
    (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero a.1) (tcpListedEdges_BAUGP P.toLocalPacketsOnB
        a.1)
    (Ac a) (cc a) (A1 a) (c1 a) (Bτ a) (cτ a)
  /-- CFS27's pruning at the reference radius. -/
  prune_eq : ∀ a, prune a = blockRestrict (firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ
      a.1))
  /-- The reference coordinates are the circle coordinates. -/
  coord_eq : ∀ a, coord a =
    cgpCircleCoord_BAUGP P.toLocalPacketsOnB a.1 ((Set.Finite.mem_toFinset _).mp a.2)
  /-- Global `C²` bounds of the pruned model. -/
  model_bounds : ∀ a u, ‖fderiv ℝ (prune a ∘ model a) u‖ ≤ tcpGraphConst ∧
    ‖fderiv ℝ (fderiv ℝ (prune a ∘ model a)) u‖ ≤ tcpGraphConst
  /-- (TG) of the pruned model on the whole reference core `B(a, 200ρ(a)) ∩ {‖η_a‖ ≤ 8}`. -/
  model_tg : ∀ a, tcpTG_PLN_BAUGP P eg (prune a ∘ model a) (coord a) a.1
  /-- The radius preimage lies in the enlargement `Ã₁` and maps to its point. -/
  rpre_spec : ∀ x : gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0,
    rpre x ∈ gafStageEnlargement_BAUGP P.toLocalPacketsOnB P.zero 0 ∧
      cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0)
          (rpre x) =
        x.1
  /-- The model preimage lies in the threshold-`7` core of its reference and maps to its point. -/
  pre_spec : ∀ x : gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0,
    pre x ∈ ball (ref x).1 (200 * ρ (ref x).1) ∧ ‖coord (ref x) (pre x)‖ ≤ 7 ∧
      cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0)
          (pre x) =
        x.1
  /-- `dim L_x = 2` and `L_x ≤ Q₁`. -/
  dimension : ∀ x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0,
    Module.finrank ℝ (toStagePlaneData_PLN.plane x) = gafStageDim 0 ∧
      toStagePlaneData_PLN.plane x ≤ gafStageQ_BAUGP P.toLocalPacketsOnB P.zero 0
  /-- FC27's (CS) for every selection of preimages, radius `Σρ(sel x)`, quality `Γ`. -/
  cloudy : ∀ sel : BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) → X,
    (∀ x ∈ gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0,
      cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0)
          (sel x) =
        x) →
    ∀ x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0,
      hausdorffEDist (gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0 ∩ ball x (sg * ρ (sel x)
          / Γ))
        ((AffineSubspace.mk' x (toStagePlaneData_PLN.plane x) :
            Set (BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²))) ∩
          ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))
  /-- TCP06's rank / normal clauses at EVERY preimage, in the units of the actual reference. -/
  normal : ∀ x (hx : x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0),
    ∀ q, cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero q = x →
      tcpNormalSpec_PLN_BAUGP P eg (toStagePlaneData_PLN.plane x) (ref ⟨x, hx⟩).1 q
  /-- EDP01's scale clause: `L_x ≤ ker v_scale`. -/
  scale_zero : ∀ x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0,
    toStagePlaneData_PLN.plane x ≤ LinearMap.ker ((blockMarkerCLM
      (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)
      (cgpScaleTag_BAUGP P.toLocalPacketsOnB P.zero) :
        BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →L[ℝ] ℝ) :
      BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →ₗ[ℝ] ℝ)
  /-- (PP): every preimage `q`, every retained marker with `ρ(c_a) < ρ(q)/5`: `L_x ≤ ker v_a`. -/
  small_pp : ∀ x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0, ∀ q,
    cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0)
        q = x →
    ∀ a : CGPMarkerIndex_BAUGP P.toLocalPacketsOnB,
      ρ (cgpMarkerCentre_BAUGP P.toLocalPacketsOnB a) < ρ q / 5 →
      toStagePlaneData_PLN.plane x ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)
        (cgpMarkerTag_BAUGP P.toLocalPacketsOnB P.zero a) :
          BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →L[ℝ] ℝ) :
        BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →ₗ[ℝ] ℝ)

section Exits

variable {P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs ζ Λz U₁ U₂ Ue₁ Ue₂} {Γ sg eg : ℝ}

end Exits


end DifferentialGeometry.Geometry.Collapse
