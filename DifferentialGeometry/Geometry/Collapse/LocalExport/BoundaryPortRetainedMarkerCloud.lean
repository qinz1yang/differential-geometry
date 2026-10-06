import DifferentialGeometry.Geometry.Fibration.ActualRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment

/-!
# Boundary port (lane B-PORT-A): ActualRetainedMarkerCloud (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualRetainedMarkerCloud.lean` by
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

section Marker

variable {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]

end Marker

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The retained constant-radius markers of `𝓔⁰` used by FC26/CFS07: circle, slim and edge
centres (the zero blocks, of radius `≥ Tρ`, are not among them). -/
abbrev CGPMarkerIndex_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) :
    Type :=
  L.circle.finite_centres.toFinset ⊕ L.slim.finite_centres.toFinset ⊕
    L.edgeB.finite_centres.toFinset

/-- The tag of a retained marker in `𝓔⁰`. -/
def cgpMarkerTag_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) :
    CGPMarkerIndex_BAUGP L → CGPTag_BAUGP L Z
  | .inl j => .inl j
  | .inr (.inl j) => .inr (.inl j)
  | .inr (.inr j) => .inr (.inr (.inl j))

/-- The centre of a retained marker. -/
def cgpMarkerCentre_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) :
    CGPMarkerIndex_BAUGP L → X
  | .inl j => j.1
  | .inr (.inl j) => j.1
  | .inr (.inr j) => j.1

/-- The normalized smooth-domain radius of a retained marker (`200`, `10⁶Δ`, `100Δ`). -/
def cgpMarkerDomain_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) :
    CGPMarkerIndex_BAUGP L → ℝ
  | .inl _ => 200
  | .inr (.inl _) => 1000000 * Δ
  | .inr (.inr _) => 100 * Δ

/-- The actual cutoff of a retained marker. -/
def cgpMarkerCutoff_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) :
    CGPMarkerIndex_BAUGP L → X → ℝ
  | .inl j => L.circle.cutoff j
  | .inr (.inl j) => L.slim.cutoff_BCNT j
  | .inr (.inr j) => L.edgeB.cutoff_BAUGA j

/-- The retained marker `y ↦ (y_i).snd` of the block space of `𝓔⁰`. -/
def cgpMarker_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ
    γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : CGPMarkerIndex_BAUGP L)
    (y : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) : ℝ :=
  (y (cgpMarkerTag_BAUGP L Z i)).snd

theorem lipschitzWith_cgpMarker_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (i : CGPMarkerIndex_BAUGP L)
        :
    LipschitzWith 1 (cgpMarker_BAUGP L Z i) :=
  lipschitzWith_blockSnd_KA2 (cgpMarkerTag_BAUGP L Z i)

/-- Every actual retained cutoff vanishes off its smooth domain `B(c_i, D_i ρ(c_i))`. -/
theorem cgpMarkerCutoff_ne_zero_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂) (hΔ : 0 < Δ)
    (i : CGPMarkerIndex_BAUGP L) (p : X) (hp : cgpMarkerCutoff_BAUGP L i p ≠ 0) :
    p ∈ ball (cgpMarkerCentre_BAUGP L i) (cgpMarkerDomain_BAUGP L i * ρ (cgpMarkerCentre_BAUGP L
        i)) := by
  rcases i with j | j | j
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h1 : (ρ j.1)⁻¹ * dist p j.1 < 200 := (L.circle.coord_lt_of_cutoff_ne_zero j.1 hj p hp).1
    rw [inv_mul_lt_iff₀ (hρ j.1)] at h1
    change dist p j.1 < 200 * ρ j.1
    linarith
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    obtain ⟨h1, h2, h3, -⟩ := fc18_slim_row_BAUGP L hΔ hj
    have h := h3 (h2 (h1 (subset_tsupport _ hp)))
    change p ∈ ball j.1 (1000000 * Δ * ρ j.1)
    convert h using 2
    norm_num
  · obtain ⟨-, hball, -, -⟩ := L.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hp
    rw [inv_mul_lt_iff₀ (hρ j.1)] at hball
    change dist p j.1 < 100 * Δ * ρ j.1
    linarith

/-- **The retained markers of `𝓔⁰`**: `marker_i(𝓔⁰ p) = ρ(c_i) ζ_i(p)`, `ζ_i` the zero extension of
the actual cutoff's restriction to the smooth domain. -/
theorem cgpMarker_globalMap_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 0 < Δ)
    (i : CGPMarkerIndex_BAUGP L) (p : X) :
    cgpMarker_BAUGP L Z i (cgpGlobalMap_BAUGP L Z p) = ρ (cgpMarkerCentre_BAUGP L i) *
      (Subtype.val : ball (cgpMarkerCentre_BAUGP L i)
        (cgpMarkerDomain_BAUGP L i * ρ (cgpMarkerCentre_BAUGP L i)) → X).extend
        (fun z => cgpMarkerCutoff_BAUGP L i z.1) 0 p := by
  rw [extend_val_restrict_eq_KA2 (cgpMarkerCutoff_ne_zero_BAUGP L hΔ i) p]
  rcases i with j | j | j <;> rfl


end DifferentialGeometry.Geometry.Collapse
