import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneFullMarker
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
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroConstantComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeetingTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroRawTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroAdaptedPhysicalTest
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K

/-!
# Boundary port (lane B-PORT-A): ActualStagePlaneFullMarker (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualStagePlaneFullMarker.lean` by
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
local instance instMetricNC14_PLNm_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNm_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNm_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section Generic

variable {κ : Type*} [Fintype κ] {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

end Generic

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **(FM\*), first stage, first half** (FD with the radius preimages, transfer to the model
preimage): for a circle chart `i` with a threshold-`7` core point `p` (`p ∈ B(i, 200ρ(i))`,
`‖η_i(p)‖ ≤ 7`), `x = 𝓔⁰(p)` and `y ∈ S₁` in the contributor window of the radius
`Σρ ∘ A.rsel x₀` (`0 ≤ Σ ≤ ε_c/10000`): the model preimage `q = A.pre y` lies in the plateau of `i`
(cutoff one, `q ∈ B(i, 200ρ(i))`, `‖η_i(q)‖ < 351/49`). -/
theorem FirstStagePlanes_PLN_BAUGP.pre_plateau_PLN_BAUGP
    {P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN_BAUGP P Γ sg eg) (hΔ : 1 ≤ Δ)
            (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalPacketsOnB.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1)) (hηp : ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB i.1
        ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7)
    {x y : BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)}
    (hpx : cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB
        P.zero 0) p =
      x)
    (hy : y ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    P.circle.cutoff i.1 (A.pre ⟨y, hy⟩) = 1 ∧ A.pre ⟨y, hy⟩ ∈ ball i.1 (200 * ρ i.1) ∧
      ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB i.1 ((Set.Finite.mem_toFinset _).mp i.2)
          (A.pre ⟨y, hy⟩)‖ < 351 / 49 := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hri := hρ i.1
  have hmemt : ∀ t : CGPTag_BAUGP P.toLocalPacketsOnB P.zero,
      t ∈ gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0 := fun t => Finset.mem_univ t
  have hp8 : p ∈ fc04Set_BAUGP P.toLocalPacketsOnB P.zero 8 := ⟨i, hpi, by
    change ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB i.1 ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 8
    linarith⟩
  have hxT : x ∈ gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0 := ⟨p, hp8, hpx⟩
  have hyT := gafCloud_subset_enlarged_BAUGP P.toLocalPacketsOnB P.zero hΔ0.le 0 hy
  have hsel := A.toStagePlaneData_PLN.rsel_spec x₀ _ fun z => (A.rpre_spec z).2
  have hselm : ∀ z ∈ gafCloudEnlarged_BAUGP P.toLocalPacketsOnB P.zero 0,
      A.rsel x₀ z ∈ fc04Set_BAUGP P.toLocalPacketsOnB P.zero 8 := fun z hz => by
    rw [A.toStagePlaneData_PLN.rsel_of_mem x₀ hz]
    exact (A.rpre_spec ⟨z, hz⟩).1
  have hrx := hsel x hxT
  have hry := hsel y hyT
  have hcutp : P.circle.cutoff i.1 p = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF_BAUGP P.toLocalPacketsOnB P.zero i hpi
      (le_trans hηp (by norm_num))
  have hfullx : cgpMarker_BAUGP P.toLocalPacketsOnB P.zero (.inl i)
      (cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0)
        (A.rsel x₀ x)) = ρ i.1 := by
    rw [hrx, ← hpx, cgpMarker_projMap_BAUGP P.toLocalPacketsOnB P.zero (hmemt _)]
    change ρ i.1 * P.circle.cutoff i.1 p = ρ i.1
    rw [hcutp, mul_one]
  have hmeet' : (closedBall (cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero
      (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0) (A.rsel x₀ y))
        (80 * εc⁻¹ * (σ * ρ (A.rsel x₀ y))) ∩
      ball (cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB
          P.zero 0)
        (A.rsel x₀ x)) (8 * εc⁻¹ * (σ * ρ (A.rsel x₀ x)))).Nonempty := by
    rw [hrx, hry]
    exact hmeet
  have hFD := gaf04_fd_projected_BAUGP P.toLocalPacketsOnB P.zero hΔ hΛ hsmall
    (fun j : P.toLocalPacketsOnB.circle.finite_centres.toFinset =>
      (.inl j : CGPMarkerIndex_BAUGP P.toLocalPacketsOnB))
    (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0) (fun _ => hmemt _)
    (fun j => {q | q ∈ ball j.1 (200 * ρ j.1) ∧
      ‖cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inl j) q‖ ≤ 8})
    (fun j q hq => hq.1)
    (fun j q hq => circle_cutoff_eq_one_of_coord_le_GAF_BAUGP P.toLocalPacketsOnB
      P.zero j hq.1 hq.2)
    (fc04Set_BAUGP P.toLocalPacketsOnB P.zero 8) (fun q hq => hq) hε hσ hσε (hselm x hxT)
    (hselm y hyT) i hfullx hmeet'
  rw [hrx, hry] at hFD
  obtain ⟨-, -, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hblk := dist_block_le_projMap_GAF_BAUGP P.toLocalPacketsOnB P.zero (hmemt (.inl i))
    (A.pre ⟨y, hy⟩) p
  rw [hqy, hpx] at hblk
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * P.circle.cutoff i.1 (A.pre ⟨y, hy⟩)) •
      cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inl i) (A.pre ⟨y, hy⟩),
      ρ i.1 * P.circle.cutoff i.1 (A.pre ⟨y, hy⟩)))
      (WithLp.toLp 2 ((ρ i.1 * 1) • cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inl i) p, ρ i.1 *
          1)) <
        ρ i.1 / 50 := by
    rw [← hcutp]
    exact lt_of_le_of_lt hblk hFD
  obtain ⟨hζ, hv⟩ := fv_of_block_dist_GAF hri le_rfl
    (by rw [mul_one]; exact hηp) hblk'
  have hcutq_ne : P.circle.cutoff i.1 (A.pre ⟨y, hy⟩) ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdom := cgpMarkerCutoff_ne_zero_BAUGP P.toLocalPacketsOnB hΔ0 (.inl i) (A.pre ⟨y, hy⟩)
      hcutq_ne
  have hv8 : ‖cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inl i) (A.pre ⟨y, hy⟩)‖ ≤ 8 := by linarith
  have hcutq : P.circle.cutoff i.1 (A.pre ⟨y, hy⟩) = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF_BAUGP P.toLocalPacketsOnB P.zero i hdom
      hv8
  exact ⟨hcutq, hdom, lt_of_lt_of_eq hv (mul_one _)⟩

open Classical in
/-- **(FM\*) at the first stage** (stage `0`): for a circle chart `i` with a threshold-`7` core
point `p` (`p ∈ B(i, 200ρ(i))`, `‖η_i(p)‖ ≤ 7`), `x = 𝓔⁰(p)` and `y ∈ S₁` in the contributor window
of the radius `Σρ ∘ A.rsel x₀`
    (`0 ≤ Σ ≤ ε_c/10000`): the circle marker of `i` is full at `y` and the
plane `A.plane y = im D(K_a ∘ Φ_a)(η_a q)` lies in its kernel (through the SAME pruning `K_a`). -/
theorem FirstStagePlanes_PLN_BAUGP.full_marker_BAUGP
    {P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN_BAUGP P Γ sg eg) (hΔ : 1 ≤ Δ)
            (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (heg0 : 0 ≤ eg) (heg : eg < 1 / 100) {εc σ : ℝ}
    (hε : 0 < εc) (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (i : P.toLocalPacketsOnB.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1)) (hηp : ‖cgpCircleCoord_BAUGP P.toLocalPacketsOnB i.1
        ((Set.Finite.mem_toFinset _).mp i.2) p‖ ≤ 7)
    {x y : BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)}
    (hpx : cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero (gafStageTags_BAUGP P.toLocalPacketsOnB
        P.zero 0) p =
      x)
    (hy : y ∈ gafCloud_BAUGP P.toLocalPacketsOnB P.zero 0)
    (hmeet : (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
      ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty) :
    cgpMarker_BAUGP P.toLocalPacketsOnB P.zero (.inl i) y = ρ i.1 ∧
      A.plane y ≤ LinearMap.ker ((blockMarkerCLM
        (V := fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²)
        (cgpMarkerTag_BAUGP P.toLocalPacketsOnB P.zero (.inl i)) :
            BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →L[ℝ] ℝ) :
          BlockSpace (fun _ : CGPTag_BAUGP P.toLocalPacketsOnB P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  have hri := hρ i.1
  have hmemt : ∀ t : CGPTag_BAUGP P.toLocalPacketsOnB P.zero,
      t ∈ gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0 := fun t => Finset.mem_univ t
  obtain ⟨hcutq, hdom, hv⟩ := A.pre_plateau_PLN_BAUGP hΔ hΛ hLΛ hε hσ hσε x₀ i hpi hηp hpx hy hmeet
  set q := A.pre ⟨y, hy⟩ with hqdef
  set a := A.ref ⟨y, hy⟩ with hadef
  obtain ⟨hqa, hηq, hqy⟩ := A.pre_spec ⟨y, hy⟩
  have hqy' : cgpProjMap_BAUGP P.toLocalPacketsOnB P.zero
      (gafStageTags_BAUGP P.toLocalPacketsOnB P.zero 0) q =
      y := hqy
  refine ⟨?_, ?_⟩
  · rw [← hqy', cgpMarker_projMap_BAUGP P.toLocalPacketsOnB P.zero (hmemt _)]
    change ρ i.1 * P.circle.cutoff i.1 q = ρ i.1
    rw [hcutq, mul_one]
  have hra := hρ a.1
  have hC : Λ * 200 ≤ 1 / 200 := by nlinarith
  have hratio := ratio_ge_of_common_point_PLN P.lipschitz_scale hΛ hra hri (mem_ball.mp hqa)
    (mem_ball.mp hdom) hC hC
  have hnum := plateau_numbers_PLN le_rfl (s := ρ i.1 / ρ a.1)
    (by rw [le_div_iff₀ hra]; linarith) heg0 heg
  have hTG := (A.model_tg a q hqa (by linarith)).1
  rw [A.toStagePlaneData_PLN.plane_of_mem hy]
  rintro _ ⟨h, rfl⟩
  rw [LinearMap.mem_ker]
  have hdiff : DifferentiableAt ℝ (A.model a) (A.coord a q) := by
    rw [A.model_eq a]
    exact ((contDiff_tcpModelGraph_BAUGP _ _ _ _ _ _ _ _ _ _ _).differentiable (by simp)) _
  change blockMarkerCLM _ (fderiv ℝ (A.prune a ∘ A.model a) (A.coord a q) h) = 0
  rw [fderiv_comp _ (A.prune a).differentiableAt hdiff, (A.prune a).fderiv,
    ContinuousLinearMap.comp_apply, A.prune_eq a, blockMarkerCLM_apply, blockRestrict_apply]
  split_ifs with hkeep
  swap
  · rfl
  rw [← blockMarkerCLM_apply, A.model_eq a]
  refine tcpModelGraph_marker_fderiv_GAFS_BAUGP P.toLocalPacketsOnB P.zero a.1 _ _ (A.Ac a) (A.cc a)
    (A.A1 a) (A.c1 a) (A.Bτ a) (A.cτ a) i (A.coord a q) (fun hlist hia => ?_) h
  have hyt : cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero q (.inl i) =
      WithLp.toLp 2 ((ρ i.1 * 1) • cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inl i) q, ρ i.1 *
          1) := by
    rw [← hcutq]
    rfl
  have hmt : (A.prune a ∘ A.model a) (A.coord a q) (.inl i) =
      scaledCutoffBlock (ρ i.1 / ρ a.1) (circleCutoffBump_LC87 : ℝ² → ℝ)
        (A.Ac a (.inl i) (A.coord a q) + A.cc a (.inl i)) := by
    change A.prune a (A.model a (A.coord a q)) (.inl i) = _
    have hkeep' : (.inl i : CGPTag_BAUGP P.toLocalPacketsOnB P.zero) ∈
        firstKeepTags_GAF5_BAUGP P.toLocalPacketsOnB P.zero (ρ a.1) := hkeep
    rw [A.prune_eq a, blockRestrict_apply, ite_eq_left hkeep', A.model_eq a]
    change tcpModelComponent_BAUGP P.toLocalPacketsOnB P.zero a.1
      (tcpListedTags_BAUGP P.toLocalPacketsOnB P.zero a.1) (tcpListedEdges_BAUGP
          P.toLocalPacketsOnB a.1)
      (A.Ac a) (A.cc a) (A.A1 a) (A.c1 a) (A.Bτ a) (A.cτ a) (.inl i) (A.coord a q) = _
    simp only [tcpModelComponent_BAUGP, hia, hlist, ite_true, ite_false]
  have hcl := block_close_PLN (.inl i) hTG hyt
  rw [hmt] at hcl
  exact scaledCutoffBlock_arg_lt_of_close_PLN (by positivity) hnum.1 hv.le hcl
    (by simpa using hnum.2)

end C14


end DifferentialGeometry.Geometry.Collapse
