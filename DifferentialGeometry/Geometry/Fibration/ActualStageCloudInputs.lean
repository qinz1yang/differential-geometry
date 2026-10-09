import DifferentialGeometry.Geometry.Fibration.ActualStageFirstTest
import DifferentialGeometry.Geometry.Fibration.ActualStageSmallMarkers
import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors

/-!
# CFS31's cloud inputs on the actual stage data

Blueprint `master207B.tex`, CFS31 (B:3783–3855), bound to the actual `𝓔⁰` with the stage clouds
`S_st = gafCloud st`, targets `Q_st = gafStageQ st` and a selection of preimages over `S̃_st`:

* `gafCloudEnlarged_fullMarker_GAF5`: every point of the enlarged stage cloud has a FULL retained
  marker `v_a(x) = R_a` (stage one: the circle cutoff is one on `‖η_j‖ ≤ 8`; stages two/three:
  FC27's full markers `fc27_edge_cloud_scale`, `fc27_slim_cloud_scale`); `gafStage_fullS_GAF5` is
  CFS31's `hfullS`.
* `gafStage_select_GAF5`: CFS31's `hselect`.
* `gafStage_core_zero_GAF5`, `gafStage_core_one_GAF5`, `gafStage_core_two_GAF5`: CFS31's `hS₀`,
  `hS₁`, `hS₂` for the family data of `gaf02_stageOne_sourceCutoff`, `gaf02_stageTwo_cutoff`,
  `gaf02_stageThree_cutoff` (domains `B(j, 200ρ)`, `B(j, 100Δρ)`, `B(j, 10⁶Δρ)`, coordinates
  `η`, `planeAxis ∘ coord`).
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

section Model

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- Stage two: every point of the enlarged edge cloud has a full edge marker. -/
theorem gafCloudEnlarged_fullMarker_one_GAF5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) :
    ∀ x ∈ gafCloudEnlarged L Z 1, ∃ a : CGPMarkerIndex L,
      blockMarkerCLM (cgpMarkerTag L Z a) x = ρ (cgpMarkerCentre L a) := by
  intro x hx
  have hx' : x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 := hx
  obtain ⟨j, hj⟩ := (fc27_edge_cloud_scale L Z hΔ hΛ hsmall).2.1 x hx'
  exact ⟨.inr (.inr j), hj⟩

/-- Stage three: every point of the enlarged slim cloud has a full slim marker. -/
theorem gafCloudEnlarged_fullMarker_two_GAF5 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) :
    ∀ x ∈ gafCloudEnlarged L Z 2, ∃ a : CGPMarkerIndex L,
      blockMarkerCLM (cgpMarkerTag L Z a) x = ρ (cgpMarkerCentre L a) := by
  intro x hx
  have hx' : x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 := hx
  obtain ⟨j, hj⟩ := (fc27_slim_cloud_scale L Z hΔ hΛ hsmall).2.1 x hx'
  exact ⟨.inr (.inl j), hj⟩

/-- CFS31's `hselect` for the actual stage data: a selection of preimages over `S̃_st` selects
preimages of the core cloud points under `π_{Q_st} ∘ 𝓔⁰`. -/
theorem gafStage_select_GAF5 (hΔ : 0 ≤ Δ) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x) :
    ∀ x ∈ gafCloud L Z st, (gafStageQ L Z st).starProjection (cgpGlobalMap L Z (sel x)) = x := by
  intro x hx
  rw [gafStageQ_starProjection_globalMap]
  exact hsel x (gafCloud_subset_enlarged L Z hΔ st hx)

/-- CFS31's `hS₀`: an original point with `‖η_j‖ < 7` on a circle chart domain has its stage-one
image in `S₁`. -/
theorem gafStage_core_zero_GAF5 :
    ∀ q, (∃ j : L.circle.finite_centres.toFinset, q ∈ ball j.1 (200 * ρ j.1) ∧
      ‖cgpCoord L Z (.inl j) q‖ < 7) →
      (gafStageQ L Z 0).starProjection (cgpGlobalMap L Z q) ∈ gafCloud L Z 0 := by
  rintro q ⟨j, hj, hη⟩
  rw [gafStageQ_starProjection_globalMap]
  exact ⟨q, ⟨j, hj, hη.le⟩, rfl⟩

/-- CFS31's `hS₁`: an original point of an edge chart domain with `|η_j| < 7Δ` and height
`< 7Δ` has its stage-two image in `S₂`. -/
theorem gafStage_core_one_GAF5 :
    ∀ q, (∃ j : L.edge.finite_centres.toFinset, q ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      ‖planeAxis (L.edge.coord j.1 q)‖ < 7 * Δ ∧ cgpHeight L q < 7 * Δ) →
      (gafStageQ L Z 1).starProjection (cgpGlobalMap L Z q) ∈ gafCloud L Z 1 := by
  rintro q ⟨j, hj, hη, ht⟩
  rw [norm_planeAxis] at hη
  rw [gafStageQ_starProjection_globalMap]
  exact ⟨q, ⟨j, hj, hη.le, ht.le⟩, rfl⟩

/-- CFS31's `hS₂`: an original point of a slim chart domain with `|η_j| < 7ℓ` (`ℓ = 10⁵Δ`) has
its stage-three image in `S₃`. -/
theorem gafStage_core_two_GAF5 :
    ∀ q, (∃ j : L.slim.finite_centres.toFinset, q ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
      ‖planeAxis ((L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord q)‖ <
        7 * (10 ^ 5 * Δ)) →
      (gafStageQ L Z 2).starProjection (cgpGlobalMap L Z q) ∈ gafCloud L Z 2 := by
  rintro q ⟨j, hj, hη⟩
  rw [norm_planeAxis] at hη
  rw [gafStageQ_starProjection_globalMap]
  refine ⟨q, ⟨j, ?_, ?_⟩, rfl⟩
  · have h6 : (10 : ℝ) ^ 6 * Δ * ρ j.1 = 1000000 * Δ * ρ j.1 := by norm_num
    rw [h6]
    exact hj
  · have h7 : (7 : ℝ) * 10 ^ 5 * Δ = 7 * (10 ^ 5 * Δ) := by ring
    rw [h7]
    exact hη.le

end Model

section Packets

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_GAF5i
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_GAF5i
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_GAF5i
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- Stage one: every point of the enlarged first cloud has a full circle marker (the circle
cutoff is one on `‖η_j‖ ≤ 8` of the chart domain). -/
theorem gafCloudEnlarged_fullMarker_zero_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) :
    ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 0,
      ∃ a : CGPMarkerIndex P.toLocalChartFamily,
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) x =
          ρ (cgpMarkerCentre P.toLocalChartFamily a) := by
  intro x hx
  rw [gafCloudEnlarged_zero_GAF4] at hx
  obtain ⟨p, ⟨j, hpj, hη⟩, rfl⟩ := hx
  refine ⟨.inl j, ?_⟩
  rw [(cgpGlobalMap_markerBlock_GAF2 P.toLocalChartFamily P.zero (.inl j) p).2]
  change ρ j.1 * P.circle.cutoff j.1 p = ρ j.1
  rw [circle_cutoff_eq_one_of_coord_le_GAF P.toLocalChartFamilyE.toLocalChartFamilyQ P.zero j hpj
    hη, mul_one]

/-- **Full markers on every enlarged stage cloud** (`1 ≤ Δ`, `0 ≤ Λ`, `10⁶ΔΛ < 10⁻⁵`). -/
theorem gafCloudEnlarged_fullMarker_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3) :
    ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      ∃ a : CGPMarkerIndex P.toLocalChartFamily,
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) x =
          ρ (cgpMarkerCentre P.toLocalChartFamily a) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by
    have h' : Λ * (1000000 * Δ) = 1000000 * Δ * Λ := by ring
    linarith
  fin_cases st
  · exact gafCloudEnlarged_fullMarker_zero_GAF5 P
  · exact gafCloudEnlarged_fullMarker_one_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall
  · exact gafCloudEnlarged_fullMarker_two_GAF5 P.toLocalChartFamily P.zero hΔ hΛ hsmall

/-- **CFS31's `hfullS` on the actual stage data**: if `π_{Q_st}𝓔⁰(q)` lies in `S_st`, some
retained marker of it is full, `v_a(π_{Q_st}𝓔⁰(q)) = R_a`. -/
theorem gafStage_fullS_GAF5
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (st : Fin 3) :
    ∀ q, (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero q) ∈ gafCloud P.toLocalChartFamily P.zero st →
      ∃ a : CGPMarkerIndex P.toLocalChartFamily,
        blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a)
          ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero q)) =
          ρ (cgpMarkerCentre P.toLocalChartFamily a) := by
  intro q hq
  have hΔ0 : 0 ≤ Δ := by linarith
  exact gafCloudEnlarged_fullMarker_GAF5 P hΔ hΛ hLΛ st _
    (gafCloud_subset_enlarged P.toLocalChartFamily P.zero hΔ0 st hq)

end Packets

end DifferentialGeometry.Geometry.Collapse
