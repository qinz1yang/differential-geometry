import DifferentialGeometry.Geometry.Fibration.ActualRetainedMarkerCloud
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyBindings

/-!
# The three actual clouds of FC07 / FC27: sets, radii and the scale comparison (MC)

Blueprint `master207B.tex`: FC04 (`lem:fibration-image-scale`, B:211), FC07
(`found:fibration-two-cloud`, B:352), FC26 (`lem:fibration-projected-radii`, B:1625), FC27
(`found:fibration-projected-clouds`, B:1658) and CFS07
(`lem:fibration-cloud-marker-scale-comparison`, B:2188), bound to CGP01's actual map
`𝓔⁰ = cgpGlobalMap L Z`. This is the cloud DATA of the three original clouds (the (CS) plane
tests themselves are produced by TCP06 / SGP06 / EGP07).

* `cgpQ2Tags`, `cgpQ3Tags`: the tags of `Q₂ = H₀ ⊕ H_s ⊕ H_e` and `Q₃ = H₀ ⊕ H_s` (FC01, B:109);
  `cgpProjMap L Z t = π_t ∘ 𝓔⁰` (`π_t = blockRestrict t`); `cgpMarker_projMap`: a projection
  retaining a whole block keeps its marker.
* `fc04Set L Z θ` (`Ã₁`: `θ = 8`, `A₁`: `θ = 7`), `fc27EdgeSet L θ` (`|η_j| ≤ θΔ`, `t ≤ θΔ`,
  `j ∈ I_e`), `fc27SlimSet L θ` (`|η_j| ≤ θ·10⁵Δ`, `j ∈ I_s`), each inside the chart's smooth
  domain.
* `scale_ratio_of_any_preimages_KA3`: CFS07's argument for ARBITRARY preimages ("independently of
  the choices", B:1639).
* `projected_cloud_scale_KA3`, `fc27_edge_cloud_scale`, `fc27_slim_cloud_scale`: (AS), full markers
  on `S̃_j = π_j𝓔⁰(Ã_j)`, FC26's radius inequality and CFS07's (MC) (`3/5 … 5/3`, `L'Σ ≤ 1/5`) for
  ANY preimages of points of `S̃_j`.
* `fc04_first_cloud_scale`: FC04's exact radius `r₁ = Σ x_ρ` on the image of `𝓔⁰`: value `Σρ`,
  `Σ`-Lipschitz, and (MC) with `B = 5/3`.
Parameter ranges: `Δ ≥ 1`, `Λ ≥ 0`, `Λ·10⁶Δ ≤ 1/4`.
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

/-- CFS07 for ANY preimages (B:2188, "does not require continuity or descent of the chosen
radius"): (AS) at every preimage with a positive marker and full markers at both image points give
`3/5 ≤ ρ(q)/ρ(p) ≤ 5/3` whenever `|f q − f p| ≤ L'·max(Σρ(q), Σρ(p))` and `L'Σ ≤ 1/5`. -/
theorem scale_ratio_of_any_preimages_KA3 (f : M → H) (ρ : M → ℝ) (marker : I → H → ℝ)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) (hLip : ∀ i, LipschitzWith 1 (marker i))
    (hAS : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    {σ L' : ℝ} (hσ : 0 ≤ σ) (hL' : 0 ≤ L') (hLσ : L' * σ ≤ 1 / 5) {p q : M} {i j : I}
    (hi : marker i (f p) = R i) (hj : marker j (f q) = R j)
    (hd : dist (f q) (f p) ≤ L' * max (σ * ρ q) (σ * ρ p)) :
    (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  have hp := hAS i p (by rw [hi]; exact hR i)
  have hq := hAS j q (by rw [hj]; exact hR j)
  have hshort : ∀ k, R i ≤ R k → R j ≤ R k → dist (f q) (f p) ≤ R k / 4 := by
    intro k hik hjk
    have hmax : max (σ * ρ q) (σ * ρ p) ≤ σ * (5 * R k / 4) :=
      max_le (mul_le_mul_of_nonneg_left (by linarith [hq.2]) hσ)
        (mul_le_mul_of_nonneg_left (by linarith [hp.2]) hσ)
    calc dist (f q) (f p) ≤ L' * (σ * (5 * R k / 4)) :=
          hd.trans (mul_le_mul_of_nonneg_left hmax hL')
      _ = (L' * σ) * (5 * R k / 4) := by ring
      _ ≤ 1 / 5 * (5 * R k / 4) := mul_le_mul_of_nonneg_right hLσ (by linarith [hR k])
      _ = R k / 4 := by ring
  have hcommon : ∃ k, 3 * R k / 4 ≤ ρ p ∧ ρ p ≤ 5 * R k / 4 ∧
      3 * R k / 4 ≤ ρ q ∧ ρ q ≤ 5 * R k / 4 := by
    rcases le_total (R j) (R i) with hji | hij
    · have hd' := hshort i le_rfl hji
      have hm := (hLip i).dist_le_mul (f q) (f p)
      rw [NNReal.coe_one, one_mul, Real.dist_eq] at hm
      have hpos : 0 < marker i (f q) := by
        have := (abs_le.mp hm).1
        linarith [hR i]
      exact ⟨i, hp.1, hp.2, hAS i q hpos⟩
    · have hd' := hshort j hij le_rfl
      have hm := (hLip j).dist_le_mul (f q) (f p)
      rw [NNReal.coe_one, one_mul, Real.dist_eq] at hm
      have hpos : 0 < marker j (f p) := by
        have := (abs_le.mp hm).2
        linarith [hR j]
      exact ⟨j, (hAS j p hpos).1, (hAS j p hpos).2, hq.1, hq.2⟩
  obtain ⟨k, h1, h2, h3, h4⟩ := hcommon
  constructor <;> linarith [hR k]

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

section Defs

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- Membership of a tag of `𝓔⁰` in `Q₂ = H₀ ⊕ H_s ⊕ H_e` (FC01, B:109). -/
def cgpInQ2 : CGPTag L Z → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- Membership of a tag of `𝓔⁰` in `Q₃ = H₀ ⊕ H_s` (FC01, B:110). -/
def cgpInQ3 : CGPTag L Z → Bool
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => false
  | .inr (.inr (.inr (.inl _))) => true
  | .inr (.inr (.inr (.inr _))) => false

/-- The tags of `Q₂`: slim, edge and zero blocks. -/
def cgpQ2Tags : Finset (CGPTag L Z) :=
  Finset.univ.filter fun t => cgpInQ2 L Z t = true

/-- The tags of `Q₃`: slim and zero blocks. -/
def cgpQ3Tags : Finset (CGPTag L Z) :=
  Finset.univ.filter fun t => cgpInQ3 L Z t = true

open Classical in
/-- `π_s 𝓔⁰`: the actual map followed by the orthogonal projection onto the blocks with tags in
`s` (`Q₂`, `Q₃` for `s = cgpQ2Tags`, `cgpQ3Tags`). -/
def cgpProjMap (t : Finset (CGPTag L Z)) (p : X) : BlockSpace (fun _ : CGPTag L Z => ℝ²) :=
  blockRestrict t (cgpGlobalMap L Z p)

/-- FC04's first-image sets `Ã₁` (`θ = 8`) and `A₁` (`θ = 7`): points of a circle chart's smooth
domain `B(j, 200ρ(j))` with `‖η_j‖ ≤ θ` (B:213). -/
def fc04Set (θ : ℝ) : Set X :=
  {p | ∃ j : L.circle.finite_centres.toFinset, p ∈ ball j.1 (200 * ρ j.1) ∧
    ‖cgpCoord L Z (.inl j) p‖ ≤ θ}

/-- FC27's edge sets (B:1660): points of an edge chart's smooth domain `B(j, 100Δρ(j))` with
`|η_j| ≤ θΔ` and `η_{E'} = t = F/ρ ≤ θΔ` (`θ = 8`: enlargement, `θ = 7`: core). -/
def fc27EdgeSet (θ : ℝ) : Set X :=
  {p | ∃ j : L.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
    |L.edge.coord j.1 p| ≤ θ * Δ ∧ cgpHeight L p ≤ θ * Δ}

/-- FC27's slim sets (B:1662): points of a slim chart's smooth domain `B(j, 10⁶Δρ(j))` with
`|η_j| ≤ θ·10⁵Δ` (`θ = 8`: enlargement, `θ = 7`: core). -/
def fc27SlimSet (θ : ℝ) : Set X :=
  {p | ∃ j : L.slim.finite_centres.toFinset, p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
    |(L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤ θ * 10 ^ 5 * Δ}

end Defs

section Proj

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

theorem cgpProjMap_apply_of_mem {t : Finset (CGPTag L Z)} {a : CGPTag L Z} (ha : a ∈ t)
    (p : X) : cgpProjMap L Z t p a = cgpGlobalMap L Z p a := by
  simp only [cgpProjMap, blockRestrict_apply, ha, ite_true]

theorem cgpMarker_projMap {t : Finset (CGPTag L Z)} {i : CGPMarkerIndex L}
    (hi : cgpMarkerTag L Z i ∈ t) (p : X) :
    cgpMarker L Z i (cgpProjMap L Z t p) = cgpMarker L Z i (cgpGlobalMap L Z p) := by
  unfold cgpMarker
  rw [cgpProjMap_apply_of_mem L Z hi]

theorem edge_mem_cgpQ2Tags (j : L.edge.finite_centres.toFinset) :
    cgpMarkerTag L Z (.inr (.inr j)) ∈ cgpQ2Tags L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem slim_mem_cgpQ3Tags (j : L.slim.finite_centres.toFinset) :
    cgpMarkerTag L Z (.inr (.inl j)) ∈ cgpQ3Tags L Z :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

end Proj

section Clouds

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- FC26 + CFS07 for a projected image `π_t 𝓔⁰` that retains the WHOLE blocks of the retained
markers `ι i`, on a cloud covered by plateau sets of those markers: (AS) at every preimage with a
positive marker, a full marker at every image point of the cloud, FC26's radius inequality and
CFS07's (MC) for ANY preimages of image points of the cloud. -/
theorem projected_cloud_scale_KA3 (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {I : Type*} (ι : I → CGPMarkerIndex L)
    (t : Finset (CGPTag L Z)) (ht : ∀ i, cgpMarkerTag L Z (ι i) ∈ t) (core : I → Set X)
    (hcore : ∀ i, core i ⊆ ball (cgpMarkerCentre L (ι i))
      (cgpMarkerDomain L (ι i) * ρ (cgpMarkerCentre L (ι i))))
    (hplateau : ∀ i p, p ∈ core i → cgpMarkerCutoff L (ι i) p = 1) (cloud : Set X)
    (hcover : ∀ p ∈ cloud, ∃ i, p ∈ core i) :
    (∀ i p, 0 < cgpMarker L Z (ι i) (cgpProjMap L Z t p) →
      3 * ρ (cgpMarkerCentre L (ι i)) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (cgpMarkerCentre L (ι i)) / 4) ∧
    (∀ x ∈ cgpProjMap L Z t '' cloud, ∃ i,
      cgpMarker L Z (ι i) x = ρ (cgpMarkerCentre L (ι i))) ∧
    (∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p q : X, cgpProjMap L Z t p ∈ cgpProjMap L Z t '' cloud →
      cgpProjMap L Z t q ∈ cgpProjMap L Z t '' cloud →
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpProjMap L Z t p) (cgpProjMap L Z t q) + sg * ρ p)) ∧
    ∀ sg L' : ℝ, 0 ≤ sg → 0 ≤ L' → L' * sg ≤ 1 / 5 → ∀ p q : X,
      cgpProjMap L Z t p ∈ cgpProjMap L Z t '' cloud →
      cgpProjMap L Z t q ∈ cgpProjMap L Z t '' cloud →
      dist (cgpProjMap L Z t q) (cgpProjMap L Z t p) ≤ L' * max (sg * ρ q) (sg * ρ p) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  have hΔ0 : 0 < Δ := by linarith
  have hD : ∀ i, cgpMarkerDomain L (ι i) = 200 ∨ cgpMarkerDomain L (ι i) = 100 * Δ ∨
      cgpMarkerDomain L (ι i) = 1000000 * Δ := by
    intro i
    rcases ι i with j | j | j
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  have hsmall' : ((Real.toNNReal Λ : NNReal) : ℝ) * (1000000 * Δ) ≤ 1 / 4 := by
    rw [Real.coe_toNNReal _ hΛ]
    exact hsmall
  have hmk : ∀ i p, cgpMarker L Z (ι i) (cgpProjMap L Z t p) =
      ρ (cgpMarkerCentre L (ι i)) *
        (Subtype.val : ball (cgpMarkerCentre L (ι i))
          (cgpMarkerDomain L (ι i) * ρ (cgpMarkerCentre L (ι i))) → X).extend
          (fun z => cgpMarkerCutoff L (ι i) z.1) 0 p := by
    intro i p
    rw [cgpMarker_projMap L Z (ht i), cgpMarker_globalMap L Z hΔ0]
  obtain ⟨hs, hf, -⟩ := original_packet_marker_scale_binding (cgpProjMap L Z t) ρ
    L.lipschitz_scale (fun i => cgpMarkerCentre L (ι i)) (fun i => cgpMarkerDomain L (ι i)) Δ hΔ
    hD hsmall' (fun i => hρ _) (fun i z => cgpMarkerCutoff L (ι i) z.1)
    (fun i => cgpMarker L Z (ι i)) hmk core hcore (fun i p hp => hplateau i p hp) cloud hcover
  have hfull : ∀ x ∈ cgpProjMap L Z t '' cloud, ∃ i,
      cgpMarker L Z (ι i) x = ρ (cgpMarkerCentre L (ι i)) := by
    rintro x ⟨p, hp, rfl⟩
    exact hf p hp
  refine ⟨hs, hfull, fun sg hsg hsg1 p q hp hq => ?_, fun sg L' hsg hL' hLsg p q hp hq hd => ?_⟩
  · exact radius_control_of_retained_markers
      (P := {z : X // cgpProjMap L Z t z ∈ cgpProjMap L Z t '' cloud})
      (fun z => cgpProjMap L Z t z.1) (fun z => ρ z.1) (fun i => cgpMarker L Z (ι i))
      (fun i => ρ (cgpMarkerCentre L (ι i))) (fun i => hρ _)
      (fun i => lipschitzWith_cgpMarker L Z (ι i)) (fun z => hfull _ z.2)
      (fun i z hz => hs i z.1 hz) hsg hsg1 ⟨p, hp⟩ ⟨q, hq⟩
  · obtain ⟨i, hi⟩ := hfull _ hp
    obtain ⟨j, hj⟩ := hfull _ hq
    exact scale_ratio_of_any_preimages_KA3 (cgpProjMap L Z t) ρ (fun i => cgpMarker L Z (ι i))
      (fun i => ρ (cgpMarkerCentre L (ι i))) (fun i => hρ _)
      (fun i => lipschitzWith_cgpMarker L Z (ι i)) hs hsg hL' hLsg hi hj hd

/-- **FC27, edge cloud data** (B:1658–1665) on the actual `𝓔⁰`: `S̃₂ = π₂𝓔⁰(Ã₂)`,
`Ã₂ = {|η_j| ≤ 8Δ, t ≤ 8Δ}` (`j ∈ I_e`) retains the whole edge blocks. (AS) for every preimage
with a positive edge marker; a full edge marker at every point of `S̃₂`; FC26's selected-radius
inequality and CFS07's (MC) for ANY preimages of points of `S̃₂`. -/
theorem fc27_edge_cloud_scale (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) :
    (∀ (j : L.edge.finite_centres.toFinset) p,
      0 < cgpMarker L Z (.inr (.inr j)) (cgpProjMap L Z (cgpQ2Tags L Z) p) →
      3 * ρ j.1 / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ j.1 / 4) ∧
    (∀ x ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8,
      ∃ j : L.edge.finite_centres.toFinset, cgpMarker L Z (.inr (.inr j)) x = ρ j.1) ∧
    (∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p q : X,
      cgpProjMap L Z (cgpQ2Tags L Z) p ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 →
      cgpProjMap L Z (cgpQ2Tags L Z) q ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 →
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpProjMap L Z (cgpQ2Tags L Z) p)
        (cgpProjMap L Z (cgpQ2Tags L Z) q) + sg * ρ p)) ∧
    ∀ sg L' : ℝ, 0 ≤ sg → 0 ≤ L' → L' * sg ≤ 1 / 5 → ∀ p q : X,
      cgpProjMap L Z (cgpQ2Tags L Z) p ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 →
      cgpProjMap L Z (cgpQ2Tags L Z) q ∈ cgpProjMap L Z (cgpQ2Tags L Z) '' fc27EdgeSet L 8 →
      dist (cgpProjMap L Z (cgpQ2Tags L Z) q) (cgpProjMap L Z (cgpQ2Tags L Z) p) ≤
        L' * max (sg * ρ q) (sg * ρ p) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  have hΔ0 : 0 < Δ := by linarith
  exact projected_cloud_scale_KA3 L Z hΔ hΛ hsmall
    (fun j : L.edge.finite_centres.toFinset => (.inr (.inr j) : CGPMarkerIndex L))
    (cgpQ2Tags L Z) (fun j => edge_mem_cgpQ2Tags L Z j)
    (fun j => {p | p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |L.edge.coord j.1 p| ≤ 8 * Δ ∧
      cgpHeight L p ≤ 8 * Δ})
    (fun j p hp => hp.1)
    (fun j p hp => L.edge.cutoff_eq_one_of_le hΔ0 ((Set.Finite.mem_toFinset _).mp j.2) hp.1
      hp.2.1 hp.2.2)
    (fc27EdgeSet L 8) (fun p hp => hp)

/-- **FC27, slim cloud data** (B:1662–1665) on the actual `𝓔⁰`: `S̃₃ = π₃𝓔⁰(Ã₃)`,
`Ã₃ = {|η_j| ≤ 8·10⁵Δ}` (`j ∈ I_s`) retains the whole slim blocks. (AS), full slim markers on `S̃₃`,
FC26's selected-radius inequality and CFS07's (MC) for ANY preimages of points of `S̃₃`. -/
theorem fc27_slim_cloud_scale (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) :
    (∀ (j : L.slim.finite_centres.toFinset) p,
      0 < cgpMarker L Z (.inr (.inl j)) (cgpProjMap L Z (cgpQ3Tags L Z) p) →
      3 * ρ j.1 / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ j.1 / 4) ∧
    (∀ x ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8,
      ∃ j : L.slim.finite_centres.toFinset, cgpMarker L Z (.inr (.inl j)) x = ρ j.1) ∧
    (∀ sg : ℝ, 0 ≤ sg → sg ≤ 1 / 2 → ∀ p q : X,
      cgpProjMap L Z (cgpQ3Tags L Z) p ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 →
      cgpProjMap L Z (cgpQ3Tags L Z) q ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 →
      |sg * ρ q - sg * ρ p| ≤ 2 * (dist (cgpProjMap L Z (cgpQ3Tags L Z) p)
        (cgpProjMap L Z (cgpQ3Tags L Z) q) + sg * ρ p)) ∧
    ∀ sg L' : ℝ, 0 ≤ sg → 0 ≤ L' → L' * sg ≤ 1 / 5 → ∀ p q : X,
      cgpProjMap L Z (cgpQ3Tags L Z) p ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 →
      cgpProjMap L Z (cgpQ3Tags L Z) q ∈ cgpProjMap L Z (cgpQ3Tags L Z) '' fc27SlimSet L 8 →
      dist (cgpProjMap L Z (cgpQ3Tags L Z) q) (cgpProjMap L Z (cgpQ3Tags L Z) p) ≤
        L' * max (sg * ρ q) (sg * ρ p) →
      (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  exact projected_cloud_scale_KA3 L Z hΔ hΛ hsmall
    (fun j : L.slim.finite_centres.toFinset => (.inr (.inl j) : CGPMarkerIndex L))
    (cgpQ3Tags L Z) (fun j => slim_mem_cgpQ3Tags L Z j)
    (fun j => {p | p ∈ ball j.1 (10 ^ 6 * Δ * ρ j.1) ∧
      |(L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| ≤ 8 * 10 ^ 5 * Δ})
    (fun j p hp => by
      have h := hp.1
      change p ∈ ball j.1 (1000000 * Δ * ρ j.1)
      rw [mem_ball] at h ⊢
      norm_num at h ⊢
      exact h)
    (fun j p hp => by
      change L.slim.cutoff j.1 p = 1
      rw [slimFamily_cutoff_eq_KA2 L ((Set.Finite.mem_toFinset _).mp j.2)]
      exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hp.1 hp.2)
    (fc27SlimSet L 8) (fun p hp => hp)

/-- **FC04 on the actual first image** (B:211): the radius `r₁ = Σ x_ρ` read from the scale block of
`𝓔⁰` is `Σρ(p)` at `𝓔⁰ p`, `Σ`-Lipschitz on `H`, and satisfies (MC) with `B = 5/3` on the whole
image (in fact `4/5 … 5/4`) whenever `L'Σ ≤ 1/5` (no sign condition on `L'` is needed). -/
theorem fc04_first_cloud_scale {L' sg : ℝ} (hsg : 0 ≤ sg) (hLsg : L' * sg ≤ 1 / 5) :
    (∀ p, scaleRadius (cgpScaleTag L Z) sg (cgpGlobalMap L Z p) = sg * ρ p) ∧
    (∀ x y : BlockSpace (fun _ : CGPTag L Z => ℝ²),
      |scaleRadius (cgpScaleTag L Z) sg x - scaleRadius (cgpScaleTag L Z) sg y| ≤ sg * dist x y) ∧
    ∀ x ∈ range (cgpGlobalMap L Z), ∀ y ∈ range (cgpGlobalMap L Z),
      dist y x ≤
        L' * max (scaleRadius (cgpScaleTag L Z) sg y) (scaleRadius (cgpScaleTag L Z) sg x) →
      scaleRadius (cgpScaleTag L Z) sg x / (5 / 3) ≤ scaleRadius (cgpScaleTag L Z) sg y ∧
        scaleRadius (cgpScaleTag L Z) sg y ≤ (5 / 3) * scaleRadius (cgpScaleTag L Z) sg x := by
  have hr : ∀ p, scaleRadius (cgpScaleTag L Z) sg (cgpGlobalMap L Z p) = sg * ρ p := by
    intro p
    rw [scaleRadius, cgpGlobalMap_scale]
  have hlip : ∀ x y : BlockSpace (fun _ : CGPTag L Z => ℝ²),
      |scaleRadius (cgpScaleTag L Z) sg x - scaleRadius (cgpScaleTag L Z) sg y| ≤
        sg * dist x y := by
    intro x y
    rw [dist_eq_norm]
    exact abs_scaleRadius_sub_le _ hsg x y
  refine ⟨hr, hlip, ?_⟩
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hd
  rw [hr, hr] at hd ⊢
  have hp := mul_nonneg hsg (hρ p).le
  have hq := mul_nonneg hsg (hρ q).le
  have h1 := hlip (cgpGlobalMap L Z p) (cgpGlobalMap L Z q)
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
