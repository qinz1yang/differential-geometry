import DifferentialGeometry.Geometry.Fibration.ActualCloudPackets
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets
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
# Boundary port (lane B-PORT-A): ActualCloudPackets (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualCloudPackets.lean` by
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

variable {M H I : Type*} [PseudoMetricSpace H]

end Generic

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

/-- Membership of a tag of `𝓔⁰` in `Q₂ = H₀ ⊕ H_s ⊕ H_e` (FC01, B:109). -/
def cgpInQ2_BAUGP : CGPTag_BAUGP L Z → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- Membership of a tag of `𝓔⁰` in `Q₃ = H₀ ⊕ H_s` (FC01, B:110). -/
def cgpInQ3_BAUGP : CGPTag_BAUGP L Z → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- The tags of `Q₂`: slim, edge and zero blocks. -/
def cgpQ2Tags_BAUGP : Finset (CGPTag_BAUGP L Z) :=
  Finset.univ.filter fun t => cgpInQ2_BAUGP L Z t = true

/-- The tags of `Q₃`: slim and zero blocks. -/
def cgpQ3Tags_BAUGP : Finset (CGPTag_BAUGP L Z) :=
  Finset.univ.filter fun t => cgpInQ3_BAUGP L Z t = true

open Classical in
/-- `π_s 𝓔⁰`: the actual map followed by the orthogonal projection onto the blocks with tags in
`s` (`Q₂`, `Q₃` for `s = cgpQ2Tags_BAUGP`, `cgpQ3Tags_BAUGP`). -/
def cgpProjMap_BAUGP (t : Finset (CGPTag_BAUGP L Z)) (p : X) : BlockSpace (fun _ : CGPTag_BAUGP L Z
    => ℝ²) :=
  blockRestrict t (cgpGlobalMap_BAUGP L Z p)

/-- FC04's first-image sets `Ã₁` (`θ = 8`) and `A₁` (`θ = 7`): points of a circle chart's smooth
domain `B(j, 200ρ(j))` with `‖η_j‖ ≤ θ` (B:213). -/
def fc04Set_BAUGP (θ : ℝ) : Set X :=
  {p | ∃ j : L.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
    ‖cgpCoord_BAUGP L Z (.inl j) p‖ ≤ θ}

/-- FC27's edge sets (B:1660): points of an edge chart's smooth domain `B(j, 100Δρ(j))` with
`|η_j| ≤ θΔ` and `η_{E'} = t = F/ρ ≤ θΔ` (`θ = 8`: enlargement, `θ = 7`: core). -/
def fc27EdgeSet_BAUGP (θ : ℝ) : Set X :=
  {p | ∃ j : L.edgeB.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
    |L.edgeB.coord_BAUGA j.1 p| ≤ θ * Δ ∧ cgpHeight_BAUGP L p ≤ θ * Δ}

/-- FC27's slim sets (B:1662): points of a slim chart's smooth domain `B(j, 10⁶Δρ(j))` with
`|η_j| ≤ θ·10⁵Δ` (`θ = 8`: enlargement, `θ = 7`: core). -/
def fc27SlimSet_BAUGP (θ : ℝ) : Set X :=
  {p | ∃ j : L.slim.finite_centres.toFinset, p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
    |(L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 p| ≤ θ * 10 ^ 5 * Δ}

end Defs

section Proj

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

theorem cgpProjMap_apply_of_mem_BAUGP {t : Finset (CGPTag_BAUGP L Z)} {a : CGPTag_BAUGP L Z} (ha :
    a ∈ t)
    (p : X) : cgpProjMap_BAUGP L Z t p a = cgpGlobalMap_BAUGP L Z p a := by
  simp only [cgpProjMap_BAUGP, blockRestrict_apply, ha, ite_true]

theorem cgpMarker_projMap_BAUGP {t : Finset (CGPTag_BAUGP L Z)} {i : CGPMarkerIndex_BAUGP L}
    (hi : cgpMarkerTag_BAUGP L Z i ∈ t) (p : X) :
    cgpMarker_BAUGP L Z i (cgpProjMap_BAUGP L Z t p) = cgpMarker_BAUGP L Z i (cgpGlobalMap_BAUGP L
        Z p) := by
  unfold cgpMarker_BAUGP
  rw [cgpProjMap_apply_of_mem_BAUGP L Z hi]

theorem edge_mem_cgpQ2Tags_BAUGP (j : L.edgeB.finite_centres.toFinset) :
    cgpMarkerTag_BAUGP L Z (.inr (.inr j)) ∈ cgpQ2Tags_BAUGP L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem slim_mem_cgpQ3Tags_BAUGP (j : L.slim.finite_centres.toFinset) :
    cgpMarkerTag_BAUGP L Z (.inr (.inl j)) ∈ cgpQ3Tags_BAUGP L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

end Proj

section Clouds

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
    V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

/-- FC26 + CFS07 for a projected image `π_t 𝓔⁰` that retains the WHOLE blocks of the retained
markers `ι i`, on a cloud covered by plateau sets of those markers: (AS) at every preimage with a
positive marker, a full marker at every image point of the cloud, FC26's radius inequality and
CFS07's (MC) for ANY preimages of image points of the cloud. -/
theorem projected_cloud_scale_KA3_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {I : Type*} (ι : I → CGPMarkerIndex_BAUGP L)
    (t : Finset (CGPTag_BAUGP L Z)) (ht : ∀ i, cgpMarkerTag_BAUGP L Z (ι i) ∈ t) (core : I → Set X)
    (hcore : ∀ i, core i ⊆ ball (cgpMarkerCentre_BAUGP L (ι i))
      (cgpMarkerDomain_BAUGP L (ι i) * ρ (cgpMarkerCentre_BAUGP L (ι i))))
    (hplateau : ∀ i p, p ∈ core i → cgpMarkerCutoff_BAUGP L (ι i) p = 1) (cloud : Set X)
    (hcover : ∀ p ∈ cloud, ∃ i, p ∈ core i) :
    (∀ i p, 0 < cgpMarker_BAUGP L Z (ι i) (cgpProjMap_BAUGP L Z t p) →
      3 * ρ (cgpMarkerCentre_BAUGP L (ι i)) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (cgpMarkerCentre_BAUGP L (ι i))
          / 4) ∧
    (∀ x ∈ cgpProjMap_BAUGP L Z t '' cloud, ∃ i,
      cgpMarker_BAUGP L Z (ι i) x = ρ (cgpMarkerCentre_BAUGP L (ι i))) ∧
    (∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p q : X, cgpProjMap_BAUGP L Z t p ∈ cgpProjMap_BAUGP L Z t
        '' cloud →
      cgpProjMap_BAUGP L Z t q ∈ cgpProjMap_BAUGP L Z t '' cloud →
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpProjMap_BAUGP L Z t p) (cgpProjMap_BAUGP L Z t q) + sg
          * ρ p)) ∧
    ∀ sg L' : ℝ, 0 ≤ sg → 0 ≤ L' → L' * sg ≤ 1 / 5 → ∀ p q : X,
      cgpProjMap_BAUGP L Z t p ∈ cgpProjMap_BAUGP L Z t '' cloud →
      cgpProjMap_BAUGP L Z t q ∈ cgpProjMap_BAUGP L Z t '' cloud →
      dist (cgpProjMap_BAUGP L Z t q) (cgpProjMap_BAUGP L Z t p) ≤ L' * max (sg * ρ q) (sg * ρ p) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  have hΔ0 : 0 < Δ := by linarith
  have hD : ∀ i, cgpMarkerDomain_BAUGP L (ι i) = 200 ∨ cgpMarkerDomain_BAUGP L (ι i) = 100 * Δ ∨
      cgpMarkerDomain_BAUGP L (ι i) = 1000000 * Δ := by
    intro i
    rcases ι i with j | j | j
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hsmall' : ((Real.toNNReal Λ : NNReal) : ℝ) * (1000000 * Δ) ≤ 1 / 4 := by
    rw [Real.coe_toNNReal _ hΛ]
    exact hsmall
  have hmk : ∀ i p, cgpMarker_BAUGP L Z (ι i) (cgpProjMap_BAUGP L Z t p) =
      ρ (cgpMarkerCentre_BAUGP L (ι i)) *
        (Subtype.val : ball (cgpMarkerCentre_BAUGP L (ι i))
          (cgpMarkerDomain_BAUGP L (ι i) * ρ (cgpMarkerCentre_BAUGP L (ι i))) → X).extend
          (fun z => cgpMarkerCutoff_BAUGP L (ι i) z.1) 0 p := by
    intro i p
    rw [cgpMarker_projMap_BAUGP L Z (ht i), cgpMarker_globalMap_BAUGP L Z hΔ0]
  obtain ⟨hs, hf, -⟩ := original_packet_marker_scale_binding (cgpProjMap_BAUGP L Z t) ρ
    L.lipschitz_scale (fun i => cgpMarkerCentre_BAUGP L (ι i)) (fun i => cgpMarkerDomain_BAUGP L (ι
        i)) Δ hΔ
    hD hsmall' (fun i => hρ _) (fun i z => cgpMarkerCutoff_BAUGP L (ι i) z.1)
    (fun i => cgpMarker_BAUGP L Z (ι i)) hmk core hcore (fun i p hp => hplateau i p hp) cloud hcover
  have hfull : ∀ x ∈ cgpProjMap_BAUGP L Z t '' cloud, ∃ i,
      cgpMarker_BAUGP L Z (ι i) x = ρ (cgpMarkerCentre_BAUGP L (ι i)) := by
    rintro x ⟨p, hp, rfl⟩
    exact hf p hp
  refine ⟨hs, hfull, fun sg hsg hsg1 p q hp hq => ?_, fun sg L' hsg hL' hLsg p q hp hq hd => ?_⟩
  · exact radius_control_of_retained_markers
      (P := {z : X // cgpProjMap_BAUGP L Z t z ∈ cgpProjMap_BAUGP L Z t '' cloud})
      (fun z => cgpProjMap_BAUGP L Z t z.1) (fun z => ρ z.1) (fun i => cgpMarker_BAUGP L Z (ι i))
      (fun i => ρ (cgpMarkerCentre_BAUGP L (ι i))) (fun i => hρ _)
      (fun i => lipschitzWith_cgpMarker_BAUGP L Z (ι i)) (fun z => hfull _ z.2)
      (fun i z hz => hs i z.1 hz) hsg hsg1 ⟨p, hp⟩ ⟨q, hq⟩
  · obtain ⟨i, hi⟩ := hfull _ hp
    obtain ⟨j, hj⟩ := hfull _ hq
    exact scale_ratio_of_any_preimages_KA3 (cgpProjMap_BAUGP L Z t) ρ (fun i => cgpMarker_BAUGP L Z
        (ι i))
      (fun i => ρ (cgpMarkerCentre_BAUGP L (ι i))) (fun i => hρ _)
      (fun i => lipschitzWith_cgpMarker_BAUGP L Z (ι i)) hs hsg hL' hLsg hi hj hd

/-- **FC27, edge cloud data** (B:1658–1665) on the actual `𝓔⁰`: `S̃₂ = π₂𝓔⁰(Ã₂)`,
`Ã₂ = {|η_j| ≤ 8Δ, t ≤ 8Δ}` (`j ∈ I_e`) retains the whole edge blocks. (AS) for every preimage
with a positive edge marker; a full edge marker at every point of `S̃₂`; FC26's selected-radius
inequality and CFS07's (MC) for ANY preimages of points of `S̃₂`. -/
theorem fc27_edge_cloud_scale_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) :
    (∀ (j : L.edgeB.finite_centres.toFinset) p,
      0 < cgpMarker_BAUGP L Z (.inr (.inr j)) (cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) p) →
      3 * ρ j.1 / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ j.1 / 4) ∧
    (∀ x ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) '' fc27EdgeSet_BAUGP L 8,
      ∃ j : L.edgeB.finite_centres.toFinset, cgpMarker_BAUGP L Z (.inr (.inr j)) x = ρ j.1) ∧
    (∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p q : X,
      cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) p ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) ''
          fc27EdgeSet_BAUGP L 8 →
      cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) q ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) ''
          fc27EdgeSet_BAUGP L 8 →
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) p)
        (cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) q) + sg * ρ p)) ∧
    ∀ sg L' : ℝ, 0 ≤ sg → 0 ≤ L' → L' * sg ≤ 1 / 5 → ∀ p q : X,
      cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) p ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) ''
          fc27EdgeSet_BAUGP L 8 →
      cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) q ∈ cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) ''
          fc27EdgeSet_BAUGP L 8 →
      dist (cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L Z) q) (cgpProjMap_BAUGP L Z (cgpQ2Tags_BAUGP L
          Z) p) ≤
        L' * max (sg * ρ q) (sg * ρ p) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  have hΔ0 : 0 < Δ := by linarith
  exact projected_cloud_scale_KA3_BAUGP L Z hΔ hΛ hsmall
    (fun j : L.edgeB.finite_centres.toFinset => (.inr (.inr j) : CGPMarkerIndex_BAUGP L))
    (cgpQ2Tags_BAUGP L Z) (fun j => edge_mem_cgpQ2Tags_BAUGP L Z j)
    (fun j => {p | p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |L.edgeB.coord_BAUGA j.1 p| ≤ 8 * Δ ∧
      cgpHeight_BAUGP L p ≤ 8 * Δ})
    (fun j p hp => hp.1)
    (fun j p hp => L.edgeB.cutoff_eq_one_of_le_BCF2K hΔ0 ((Set.Finite.mem_toFinset _).mp j.2) hp.1
      hp.2.1 hp.2.2)
    (fc27EdgeSet_BAUGP L 8) (fun p hp => hp)

/-- **FC27, slim cloud data** (B:1662–1665) on the actual `𝓔⁰`: `S̃₃ = π₃𝓔⁰(Ã₃)`,
`Ã₃ = {|η_j| ≤ 8·10⁵Δ}` (`j ∈ I_s`) retains the whole slim blocks. (AS), full slim markers on `S̃₃`,
FC26's selected-radius inequality and CFS07's (MC) for ANY preimages of points of `S̃₃`. -/
theorem fc27_slim_cloud_scale_BAUGP (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) :
    (∀ (j : L.slim.finite_centres.toFinset) p,
      0 < cgpMarker_BAUGP L Z (.inr (.inl j)) (cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) p) →
      3 * ρ j.1 / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ j.1 / 4) ∧
    (∀ x ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) '' fc27SlimSet_BAUGP L 8,
      ∃ j : L.slim.finite_centres.toFinset, cgpMarker_BAUGP L Z (.inr (.inl j)) x = ρ j.1) ∧
    (∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p q : X,
      cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) p ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) ''
          fc27SlimSet_BAUGP L 8 →
      cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) q ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) ''
          fc27SlimSet_BAUGP L 8 →
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) p)
        (cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) q) + sg * ρ p)) ∧
    ∀ sg L' : ℝ, 0 ≤ sg → 0 ≤ L' → L' * sg ≤ 1 / 5 → ∀ p q : X,
      cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) p ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) ''
          fc27SlimSet_BAUGP L 8 →
      cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) q ∈ cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) ''
          fc27SlimSet_BAUGP L 8 →
      dist (cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L Z) q) (cgpProjMap_BAUGP L Z (cgpQ3Tags_BAUGP L
          Z) p) ≤
        L' * max (sg * ρ q) (sg * ρ p) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  exact projected_cloud_scale_KA3_BAUGP L Z hΔ hΛ hsmall
    (fun j : L.slim.finite_centres.toFinset => (.inr (.inl j) : CGPMarkerIndex_BAUGP L))
    (cgpQ3Tags_BAUGP L Z) (fun j => slim_mem_cgpQ3Tags_BAUGP L Z j)
    (fun j => {p | p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
      |(L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 p| ≤ 8 * 10 ^ 5 * Δ})
    (fun j p hp => by
      have h := hp.1
      change p ∈ ball j.1 (1000000 * Δ * ρ j.1)
      rw [mem_ball] at h ⊢
      norm_num at h ⊢
      exact h)
    (fun j p hp => by
      change L.slim.cutoff_BCNT j.1 p = 1
      rw [slimFamily_cutoff_eq_KA2_BAUGP L ((Set.Finite.mem_toFinset _).mp j.2)]
      exact SlimCentreOn.cutoff_eq_one_of_abs_coord_le_BAUGP _ hp.1 hp.2)
    (fc27SlimSet_BAUGP L 8) (fun p hp => hp)

/-- **FC04 on the actual first image** (B:211): the radius `r₁ = Σ x_ρ` read from the scale block of
`𝓔⁰` is `Σρ(p)` at `𝓔⁰ p`, `Σ`-Lipschitz on `H`, and satisfies (MC) with `B = 5/3` on the whole
image (in fact `4/5 … 5/4`) whenever `L'Σ ≤ 1/5` (no sign condition on `L'` is needed). -/
theorem fc04_first_cloud_scale_BAUGP {L' sg : ℝ} (hsg : 0 ≤ sg) (hLsg : L' * sg ≤ 1 / 5) :
    (∀ p, scaleRadius (cgpScaleTag_BAUGP L Z) sg (cgpGlobalMap_BAUGP L Z p) = sg * ρ p) ∧
    (∀ x y : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²),
      |scaleRadius (cgpScaleTag_BAUGP L Z) sg x - scaleRadius (cgpScaleTag_BAUGP L Z) sg y| ≤ sg *
          dist x y) ∧
    ∀ x ∈ range (cgpGlobalMap_BAUGP L Z), ∀ y ∈ range (cgpGlobalMap_BAUGP L Z),
      dist y x ≤
        L' * max (scaleRadius (cgpScaleTag_BAUGP L Z) sg y) (scaleRadius (cgpScaleTag_BAUGP L Z) sg
            x) →
      scaleRadius (cgpScaleTag_BAUGP L Z) sg x / (5 / 3) ≤ scaleRadius (cgpScaleTag_BAUGP L Z) sg y
          ∧
        scaleRadius (cgpScaleTag_BAUGP L Z) sg y ≤ (5 / 3) * scaleRadius (cgpScaleTag_BAUGP L Z) sg
            x := by
  have hr : ∀ p, scaleRadius (cgpScaleTag_BAUGP L Z) sg (cgpGlobalMap_BAUGP L Z p) = sg * ρ p := by
    intro p
    rw [scaleRadius, cgpGlobalMap_scale_BAUGP]
  have hlip : ∀ x y : BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²),
      |scaleRadius (cgpScaleTag_BAUGP L Z) sg x - scaleRadius (cgpScaleTag_BAUGP L Z) sg y| ≤
        sg * dist x y := by
    intro x y
    rw [dist_eq_norm]
    exact abs_scaleRadius_sub_le _ hsg x y
  refine ⟨hr, hlip, ?_⟩
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hd
  rw [hr, hr] at hd ⊢
  have hp := mul_nonneg hsg (hρ p).le
  have hq := mul_nonneg hsg (hρ q).le
  have h1 := hlip (cgpGlobalMap_BAUGP L Z p) (cgpGlobalMap_BAUGP L Z q)
  rw [hr, hr, dist_comm] at h1
  have h2 : |sg * ρ p - sg * ρ q| ≤ max (sg * ρ q) (sg * ρ p) / 5 := by
    calc |sg * ρ p - sg * ρ q| ≤ sg * (L' * max (sg * ρ q) (sg * ρ p)) :=
          h1.trans (mul_le_mul_of_nonneg_left hd hsg)
      _ = (L' * sg) * max (sg * ρ q) (sg * ρ p) := by ring
      _ ≤ 1 / 5 * max (sg * ρ q) (sg * ρ p) :=
          mul_le_mul_of_nonneg_right hLsg (le_max_of_le_left hq)
      _ = max (sg * ρ q) (sg * ρ p) / 5 := by ring
  obtain ⟨hlo, hhi⟩ := abs_le.mp h2
  rcases le_total (sg * ρ q) (sg * ρ p) with hqp | hpq
  · rw [max_eq_right hqp] at hlo hhi
    constructor <;> linarith
  · rw [max_eq_left hpq] at hlo hhi
    constructor <;> linarith

end Clouds


end DifferentialGeometry.Geometry.Collapse
