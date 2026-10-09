import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneZeroBlock
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStagePlaneTypes
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageSmallMarkers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortStageTargets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroBlockIsolation
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeetingTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroRawTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroAdaptedPhysicalTest
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualStagePlaneZeroBlock (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStagePlaneZeroBlock.lean` by
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
local instance instMetricNC14_PLNz_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNz_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNz_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The scale chain of (ZB\*)**: for a selection `sel` over `S̃_st`, a preimage `p` of
`x ∈ S_st`, a preimage `q` of `y ∈ S_st` and the window
`B̄(y, 80ε⁻¹Σρ(sel y)) ∩ B(x, 8ε⁻¹Σρ(sel x)) ≠ ∅` (`Σ ≤ ε/10000`): `ρ(q) ≥ (27/125)ρ(p)`
((MCb) with `L' = 88ε⁻¹` and CFS26's two-preimage ratio twice). -/
theorem zero_chain_PLN_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged_BAUGP L Z st, cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st)
        (sel x) = x)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) {p q : X}
    {x y : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)}
    (hpx : cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st) p = x) (hx : x ∈ gafCloud_BAUGP L Z st)
    (hy : y ∈ gafCloud_BAUGP L Z st) (hqy : cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st) q = y)
    (hmeet : (closedBall y (80 * εc⁻¹ * (σ * ρ (sel y))) ∩
      ball x (8 * εc⁻¹ * (σ * ρ (sel x)))).Nonempty) :
    27 / 125 * ρ p ≤ ρ q := by
  classical
  obtain ⟨z, hz1, hz2⟩ := hmeet
  have hεi : 0 < εc⁻¹ := inv_pos.mpr hε
  have hrx := hρ (sel x)
  have hry := hρ (sel y)
  have h1 := mem_closedBall.mp hz1
  have h2 := mem_ball.mp hz2
  have hσ : 0 < σ := by
    by_contra h
    push Not at h
    have h3 : σ * ρ (sel x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hrx.le
    have h4 : 8 * εc⁻¹ * (σ * ρ (sel x)) ≤ 0 := by nlinarith
    linarith [dist_nonneg (x := z) (y := x)]
  have hd : dist y x ≤ 88 * εc⁻¹ * max (σ * ρ (sel y)) (σ * ρ (sel x)) := by
    have h3 : dist y x ≤ dist z y + dist z x := dist_triangle_left y x z
    have hm1 : σ * ρ (sel y) ≤ max (σ * ρ (sel y)) (σ * ρ (sel x)) := le_max_left _ _
    have hm2 : σ * ρ (sel x) ≤ max (σ * ρ (sel y)) (σ * ρ (sel x)) := le_max_right _ _
    nlinarith
  have hΔ0 : (0 : ℝ) ≤ Δ := by linarith
  have hxT := gafCloud_subset_enlarged_BAUGP L Z hΔ0 st hx
  have hyT := gafCloud_subset_enlarged_BAUGP L Z hΔ0 st hy
  have hLs : 88 * εc⁻¹ * σ ≤ 1 / 5 := by
    have : εc⁻¹ * σ ≤ 1 / 10000 := by
      rw [inv_mul_le_iff₀ hε]
      linarith
    nlinarith
  have hmcb := (gafCloud_mcb_GAF2_BAUGP L Z hΔ hΛ hsmall st sel hsel hσ.le (by positivity) hLs x
      hxT y
    hyT hd).1
  have h5 : 3 / 5 * ρ (sel x) ≤ ρ (sel y) := by
    have h6 : σ * (3 / 5 * ρ (sel x)) ≤ σ * ρ (sel y) := by
      have : σ * ρ (sel x) / (5 / 3) = σ * (3 / 5 * ρ (sel x)) := by ring
      linarith
    exact le_of_mul_le_mul_left h6 hσ
  have h7 := gafCloud_preimage_ratio_GAF4_BAUGP L Z hΔ hΛ hsmall st sel hsel x hx p
    (by rw [gafStageQ_starProjection_globalMap_BAUGP]; exact hpx)
  have hsel' : ∀ w ∈ gafCloudEnlarged_BAUGP L Z st,
      cgpProjMap_BAUGP L Z (gafStageTags_BAUGP L Z st) (Function.update sel y q w) = w := by
    intro w hw
    by_cases hwy : w = y
    · subst hwy
      rw [Function.update_self]
      exact hqy
    · rw [Function.update_of_ne hwy]
      exact hsel w hw
  have h8 := gafCloud_preimage_ratio_GAF4_BAUGP L Z hΔ hΛ hsmall st (Function.update sel y q) hsel'
      y hy
    (sel y) (by rw [gafStageQ_starProjection_globalMap_BAUGP]; exact hsel y hyT)
  rw [Function.update_self] at h8
  nlinarith

end Generic

section R

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricNR_PLNz_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsR`, as a named local instance. -/
local instance instChartedNR_PLNz_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsR`, as a named local instance. -/
local instance instMetricCR_PLNz_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **No zero support meets a large reference**: if `ρ(a) > (80/3)R_k/T`, no point `z` of the closed
support of the zero cutoff of `k` lies in `B(a, Cρ(a))` with `ΛC ≤ 1/4` (LPA05: `ρ(z) ≤ 20R_k/T`;
slow variation: `ρ(z) ≥ (3/4)ρ(a)`). -/
theorem zero_meet_absurd_PLN_BAUGP
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂)
    (hΛ : 0 ≤ Λ) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr) {k : X}
    (hk : k ∈ P.zero.centres) {a z : X} {Cr : ℝ}
    (hz : z ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)))
    (hza : dist z a < Cr * ρ a) (hC : Λ * Cr ≤ 1 / 4)
    (hρa : 80 / 3 * ((P.zero.zero k hk).radius / T) < ρ a) : False := by
  have h1 := zero_cutoff_ratio_GAF_BAUGP P hT he hεr hk hz
  have h2 := (scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ a) hza hC).1
  have h3 : 20 * (P.zero.zero k hk).radius / T = 20 * ((P.zero.zero k hk).radius / T) := by ring
  linarith

end R

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

open Classical in
/-- **(ZB\*) at the first stage**: for a zero tag `k`, a preimage `p` of `x ∈ S` with
`ρ(p) > 200R_k/T` and `y ∈ S` in the contributor window of the radius `Σρ ∘ A.rsel x₀`
(`Σ ≤ ε_c/10000`): the whole `k`-block of `y` vanishes and `A.plane y ≤ ker J_k`. -/
theorem FirstStagePlanes_PLN_BAUGP.zero_block_BAUGP
    {P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN_BAUGP P Γ sg eg) (hΔ : 1 ≤ Δ)
            (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (k : P.zero.finite_centres.toFinset) {p : X} {x y :
        BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)}
    (hpx : cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB
        P.zero 0) p =
      x) (hx : x ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0)
    (hρp : 200 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T < ρ p)
    (hy : y ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    blockProjCLM_PLN (V
        := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) y =
            0 ∧
      A.plane y ≤ LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have hR := (P.zero.zero k.1 hk).radius_pos
  have hRT : 0 < (P.zero.zero k.1 hk).radius / T := div_pos hR hT
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, -, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB
      P.zero 0)
      q = y := hqy
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hchain := zero_chain_PLN_BAUGP P.toLocalPacketsOnB P.zero hΔ hΛ hsmall 0 (A.rsel x₀) hsel hε
    hσε hpx hx hy hqy' hmeet
  have hρp' : 200 * ((P.zero.zero k.1 hk).radius / T) < ρ p := by
    have : 200 * (P.zero.zero k.1 hk).radius / T = 200 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    linarith
  have hρq : 20 * (P.zero.zero k.1 hk).radius / T < ρ q := by
    have : 20 * (P.zero.zero k.1 hk).radius / T = 20 * ((P.zero.zero k.1 hk).radius / T) := by
      ring
    nlinarith
  have hsa := scale_mem_of_dist_lt_KC P.lipschitz_scale hΛ (hρ a.1) (mem_ball.mp hqa)
    (by nlinarith : Λ * (200) ≤ 1 / 4)
  have hρa : 80 / 3 * ((P.zero.zero k.1 hk).radius / T) < ρ a.1 := by nlinarith
  refine ⟨?_, ?_⟩
  · have hz := zsp01_original_zero_block_BAUGP P hT he hεr k hρq
    rw [blockProjCLM_apply_PLN, ← hqy']
    change blockRestrict _ (cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero q) _ = 0
    rw [blockRestrict_apply]
    split_ifs
    · exact hz
    · rfl
  have habs : (.inr (.inr (.inr (.inl k))) : CGPTag_BAUGP P.toLocalPacketsOnB P.zero) ∉
      tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero a.1 := by
    intro h
    obtain ⟨z, hz, hza⟩ := (mem_tcpListedTags_KA7_BAUGP (i := a.1)).mp h
    exact zero_meet_absurd_PLN_BAUGP P hΛ hT he hεr hk hz (mem_ball.mp hza)
      (by nlinarith) hρa
  rw [A.toStagePlaneData_PLN.plane_of_mem hy]
  refine stagePlane_le_ker_proj_PLN A.model A.prune A.coord a q _ ?_
    (Eventually.of_forall fun u => ?_)
  · refine (A.prune a).differentiableAt.comp _ ?_
    rw [A.model_eq a]
    exact ((contDiff_tcpModelGraph_BAUGP _ _ _ _ _ _ _ _ _ _ _).differentiable (by simp)) _
  · beta_reduce
    rw [A.prune_eq a, A.model_eq a, Function.comp_apply, blockRestrict_apply]
    split_ifs
    · change tcpModelComponent_BAUGP P.toLocalPacketsOnB P.zero a.1
        (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero a.1) (tcpListedEdges_BAUGP
            P.toLocalPacketsOnB a.1)
        (A.Ac a) (A.cc a) (A.A1 a) (A.c1 a) (A.Bτ a) (A.cτ a) (.inr (.inr (.inr (.inl k)))) u = 0
      simp only [tcpModelComponent_BAUGP, habs, ite_false]
      rfl
    · rfl

open Classical in
/-- **Whole small block, first stage** (CGP04): a marker block with `ρ(c) ≤ ρ(a)/2` is deleted by
`K_a`, so the WHOLE block of `K_a ∘ Φ_a` vanishes. -/
theorem FirstStagePlanes_PLN_BAUGP.small_block_zero_BAUGP
    {P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN_BAUGP P Γ sg eg)
    (a : P.toLocalPacketsOnB.circle.finite_centres.toFinset)
        (c : CGPMarkerIndex_BAUGP P.toLocalPacketsOnB)
    (hc : ρ (cgpMarkerCentre_BAUGP P.toLocalPacketsOnB c) ≤ ρ a.1 / 2) (u : ℝ²) :
    (A.prune a ∘ A.model a) u (cgpMarkerTag_BAUGP P.toLocalPacketsOnB P.zero c) = 0 := by
  rw [Function.comp_apply, A.prune_eq a, blockRestrict_apply,
    ite_eq_right (firstKeep_marker_GAF5_BAUGP P.toLocalPacketsOnB P.zero c hc)]

end C14


end DifferentialGeometry.Geometry.Collapse
