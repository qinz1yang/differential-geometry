import DifferentialGeometry.Geometry.Fibration.ActualCloudPacketsApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualCloudPacketsApplications (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualCloudPacketsApplications.lean` by
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- (MCb) on the actual edge cloud `S̃₂` for ANY selection of preimages. -/
theorem fc27_edge_cloud_mcb_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (select : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) '' fc27EdgeSet_BAUGP L 8,
      cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) (select x) = x)
    {sg L' : ℝ} (hsg : 0 ≤ sg) (hL' : 0 ≤ L') (hLsg : L' * sg ≤ 1 / 5) :
    ∀ x ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) '' fc27EdgeSet_BAUGP L 8,
      ∀ y ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) '' fc27EdgeSet_BAUGP L 8,
        dist y x ≤ L' * max (sg * ρ (select y)) (sg * ρ (select x)) →
        sg * ρ (select x) / (5 / 3) ≤ sg * ρ (select y) ∧
          sg * ρ (select y) ≤ (5 / 3) * (sg * ρ (select x)) := by
  intro x hx y hy hd
  have hx' := hselect x hx
  have hy' := hselect y hy
  refine selected_radius_ratio_KA3 hsg ((fc27_edge_cloud_scale_BAUGP L Z hΔ hΛ hsmall).2.2.2 sg L'
    hsg hL' hLsg (select x) (select y) (by rw [hx']; exact hx) (by rw [hy']; exact hy) ?_)
  rw [hx', hy']
  exact hd

/-- (MCb) on the actual slim cloud `S̃₃` for ANY selection of preimages. -/
theorem fc27_slim_cloud_mcb_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (select : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) → X)
    (hselect : ∀ x ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) '' fc27SlimSet_BAUGP L 8,
      cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) (select x) = x)
    {sg L' : ℝ} (hsg : 0 ≤ sg) (hL' : 0 ≤ L') (hLsg : L' * sg ≤ 1 / 5) :
    ∀ x ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) '' fc27SlimSet_BAUGP L 8,
      ∀ y ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) '' fc27SlimSet_BAUGP L 8,
        dist y x ≤ L' * max (sg * ρ (select y)) (sg * ρ (select x)) →
        sg * ρ (select x) / (5 / 3) ≤ sg * ρ (select y) ∧
          sg * ρ (select y) ≤ (5 / 3) * (sg * ρ (select x)) := by
  intro x hx y hy hd
  have hx' := hselect x hx
  have hy' := hselect y hy
  refine selected_radius_ratio_KA3 hsg ((fc27_slim_cloud_scale_BAUGP L Z hΔ hΛ hsmall).2.2.2 sg L'
    hsg hL' hLsg (select x) (select y) (by rw [hx']; exact hx) (by rw [hy']; exact hy) ?_)
  rw [hx', hy']
  exact hd

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_KA3_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_KA3_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_KA3_BAUGP
    (P : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a


end DifferentialGeometry.Geometry.Collapse
