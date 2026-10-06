import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors
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
# Boundary port (lane B-PORT-A): ActualFullMarkerContributors (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualFullMarkerContributors.lean` by
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

section Generic

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

section FD

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

/-- **(FD)** of GAF04 for a projected actual cloud: retained markers `ι i` with whole blocks in
`t`, plateau cores covering the cloud; with `Σ ≤ ε/10000`, `b = εc⁻¹`, any contributor whose closed
`80bΣρ` ball meets the `8bΣρ` ball of a full-`i`-marker cloud point is within `R_i/50`. -/
theorem gaf04_fd_projected_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    {I : Type*} (ι : I → CGPMarkerIndex_BAUGP L) (t : Finset (CGPTag_BAUGP L Z))
    (ht : ∀ i, cgpMarkerTag_BAUGP L Z (ι i) ∈ t) (core : I → Set X)
    (hcore : ∀ i, core i ⊆ ball (cgpMarkerCentre_BAUGP L (ι i))
      (cgpMarkerDomain_BAUGP L (ι i) * ρ (cgpMarkerCentre_BAUGP L (ι i))))
    (hplateau : ∀ i p, p ∈ core i → cgpMarkerCutoff_BAUGP L (ι i) p = 1) (cloud : Set X)
    (hcover : ∀ p ∈ cloud, ∃ i, p ∈ core i) {εc σ : ℝ} (hε : 0 < εc) (hσ : 0 ≤ σ)
    (hσε : σ ≤ εc / 10000) {px pu : X} (hpx : px ∈ cloud) (hpu : pu ∈ cloud) (i : I)
    (hfullx : cgpMarker_BAUGP L Z (ι i) (cgpProjMap_BAUGP L Z t px) = ρ (cgpMarkerCentre_BAUGP L (ι
        i)))
    (hmeet : (closedBall (cgpProjMap_BAUGP L Z t pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
      ball (cgpProjMap_BAUGP L Z t px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty) :
    dist (cgpProjMap_BAUGP L Z t pu) (cgpProjMap_BAUGP L Z t px) < ρ (cgpMarkerCentre_BAUGP L (ι
        i)) / 50 := by
  obtain ⟨hs, hfull, -, -⟩ :=
    projected_cloud_scale_KA3_BAUGP L Z hΔ hΛ hsmall ι t ht core hcore hplateau cloud hcover
  exact contributor_dist_lt_fiftieth_of_full_marker (P := cloud)
    (fun z => cgpProjMap_BAUGP L Z t z.1) (fun z => ρ z.1) (fun i => cgpMarker_BAUGP L Z (ι i))
    (fun i => ρ (cgpMarkerCentre_BAUGP L (ι i))) (fun _ => hρ _)
    (fun i => lipschitzWith_cgpMarker_BAUGP L Z (ι i)) (fun z => hfull _ ⟨z.1, z.2, rfl⟩)
    (fun i z hz => hs i z.1 hz) hε hσ hσε ⟨px, hpx⟩ ⟨pu, hpu⟩ i hfullx hmeet

/-- The projection onto all tags is the identity: `π_univ 𝓔⁰ = 𝓔⁰`. -/
theorem cgpProjMap_univ_GAF_BAUGP : cgpProjMap_BAUGP L Z Finset.univ = cgpGlobalMap_BAUGP L Z := by
  funext p
  refine PiLp.ext fun a => ?_
  simp only [cgpProjMap_BAUGP, blockRestrict_apply, Finset.mem_univ, ite_true]

/-- The block of a retained tag of `π_t 𝓔⁰` is controlled by the distance of the images. -/
theorem dist_block_le_projMap_GAF_BAUGP {t : Finset (CGPTag_BAUGP L Z)} {a : CGPTag_BAUGP L Z} (ha
    : a ∈ t)
    (p q : X) :
    dist (cgpGlobalMap_BAUGP L Z p a) (cgpGlobalMap_BAUGP L Z q a) ≤
      dist (cgpProjMap_BAUGP L Z t p) (cgpProjMap_BAUGP L Z t q) := by
  rw [← cgpProjMap_apply_of_mem_BAUGP L Z ha p, ← cgpProjMap_apply_of_mem_BAUGP L Z ha q]
  exact PiLp.dist_apply_le _ _ a

end FD

section Stages

/-- The LC87 circle cutoff is one where `‖η_j‖ ≤ 8` on the chart domain `B(j, 200ρ(j))`. -/
theorem circle_cutoff_eq_one_of_coord_le_GAF_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)
    (j : L.circle.finite_centres.toFinset) {p : X} (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord_BAUGP L Z (.inl j) p‖ ≤ 8) : L.circle.cutoff j.1 p = 1 := by
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have h := L.circle_cutoff_apply_BAUGP hj p
  simp only [mem_ball.mp hp, ↓reduceIte] at h
  rw [h]
  refine circleCutoffBump_LC87.one_of_mem_closedBall ?_
  rw [mem_closedBall, dist_zero_right]
  exact hη

end Stages


end DifferentialGeometry.Geometry.Collapse
