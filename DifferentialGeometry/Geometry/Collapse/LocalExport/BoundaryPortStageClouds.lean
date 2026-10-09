import DifferentialGeometry.Geometry.Fibration.ActualStageClouds
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualStageClouds (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStageClouds.lean` by
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

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

section Defs

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

/-- The tag sets of the three stage targets: `Q₁ = H` (all tags), `Q₂`, `Q₃`. -/
def gafStageTags_BAUGP : Fin 3 → Finset (CGPTag_BAUGP L Z) := ![Finset.univ, cgpQ2Tags_BAUGP L Z,
    cgpQ3Tags_BAUGP L Z]

/-- The original cores `A_j` of the three stages (threshold `7`). -/
def gafStageCore_BAUGP : Fin 3 → Set X := ![fc04Set_BAUGP L Z 7, fc27EdgeSet_BAUGP L 7,
    fc27SlimSet_BAUGP L 7]

/-- The original enlargements `Ã_j` of the three stages (threshold `8`). -/
def gafStageEnlargement_BAUGP : Fin 3 → Set X := ![fc04Set_BAUGP L Z 8, fc27EdgeSet_BAUGP L 8,
    fc27SlimSet_BAUGP L 8]

/-- The actual stage cloud `S_j = π_j𝓔⁰(A_j)`. -/
def gafCloud_BAUGP (st : Fin 3) : Set (BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) :=
  cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st) '' gafStageCore_BAUGP L Z st

/-- The actual enlarged stage cloud `S̃_j = π_j𝓔⁰(Ã_j)`. -/
def gafCloudEnlarged_BAUGP (st : Fin 3) : Set (BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) :=
  cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st) '' gafStageEnlargement_BAUGP L Z st

theorem gafCloud_subset_enlarged_BAUGP (hΔ : 0 ≤ Δ) (st : Fin 3) :
    gafCloud_BAUGP L Z st ⊆ gafCloudEnlarged_BAUGP L Z st := by
  refine image_mono ?_
  fin_cases st
  · exact fc04Set_mono_BAUGP L Z (by norm_num)
  · exact fc27EdgeSet_mono_BAUGP L hΔ (by norm_num)
  · exact fc27SlimSet_mono_BAUGP L hΔ (by norm_num)

end Defs

/-- (MCb) at stage `st` for the selected radius `Σρ ∘ sel`, any selection of preimages over the
enlarged stage cloud, any buffer `L' ≥ 0` with `L'Σ ≤ 1/5`. -/
theorem gafCloud_mcb_GAF2_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged_BAUGP L Z st, cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st)
        (sel x) = x)
    {sg L' : ℝ} (hsg : 0 ≤ sg) (hL' : 0 ≤ L') (hLsg : L' * sg ≤ 1 / 5) :
    ∀ x ∈ gafCloudEnlarged_BAUGP L Z st, ∀ y ∈ gafCloudEnlarged_BAUGP L Z st,
      dist y x ≤ L' * max (sg * ρ (sel y)) (sg * ρ (sel x)) →
      sg * ρ (sel x) / (5 / 3) ≤ sg * ρ (sel y) ∧ sg * ρ (sel y) ≤ (5 / 3) * (sg * ρ (sel x)) := by
  fin_cases st
  · intro x hx y hy hd
    have huniv := cgpProjMap_univ_GAF_BAUGP L Z
    have hx' : cgpGlobalMap_BAUGP L Z (sel x) = x := by
      rw [← huniv]
      exact hsel x hx
    have hy' : cgpGlobalMap_BAUGP L Z (sel y) = y := by
      rw [← huniv]
      exact hsel y hy
    obtain ⟨hr, -, hmc⟩ := fc04_first_cloud_scale_BAUGP L Z hsg hLsg
    have hrx : scaleRadius (cgpScaleTag_BAUGP L Z) sg x = sg * ρ (sel x) := by
      rw [← hr, hx']
    have hry : scaleRadius (cgpScaleTag_BAUGP L Z) sg y = sg * ρ (sel y) := by
      rw [← hr, hy']
    have h := hmc x ⟨sel x, hx'⟩ y ⟨sel y, hy'⟩ (by rw [hrx, hry]; exact hd)
    rwa [hrx, hry] at h
  · exact fc27_edge_cloud_mcb_BAUGP L Z hΔ hΛ hsmall sel hsel hsg hL' hLsg
  · exact fc27_slim_cloud_mcb_BAUGP L Z hΔ hΛ hsmall sel hsel hsg hL' hLsg

variable {Lmax τ γ : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNSC_GAF2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNSC_GAF2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCSC_GAF2_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a


end DifferentialGeometry.Geometry.Collapse
