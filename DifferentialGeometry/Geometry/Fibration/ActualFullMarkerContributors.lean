import DifferentialGeometry.Geometry.Fibration.ActualCloudPackets
import DifferentialGeometry.Geometry.Metric.FullMarkerContributors
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyQuantitativeApplications

/-!
# GAF04 on the three actual clouds of `𝓔⁰`: (FD), (FV) and the exact contributor marker

Blueprint `master207B.tex`, GAF04 (`lem:fibration-actual-full-marker-contributors`, B:5896–5970),
bound to CGP01's actual map `𝓔⁰ = cgpGlobalMap L Z` and the three actual clouds of C14-KA3
(`ActualCloudPackets.lean`): the first cloud `𝓔⁰(Ã₁)` (`fc04Set L Z 8`, no projection), the edge
cloud `π₂𝓔⁰(Ã₂)` (`fc27EdgeSet L 8`, `Q₂`) and the slim cloud `π₃𝓔⁰(Ã₃)` (`fc27SlimSet L 8`, `Q₃`);
radii `r = Σρ` at any preimage, `b = εc⁻¹`, `Σ ≤ ε/10000`.

* `gaf04_fd_projected`: (FD) for any projection retaining the whole blocks of a retained marker
  family on a cloud covered by plateau cores: a cloud point whose closed `80br` ball meets the
  `8br_x` ball of a full-`i`-marker cloud point is within `R_i/50` (kernel
  `contributor_dist_lt_fiftieth_of_full_marker`, inputs from `projected_cloud_scale_KA3`).
* `gaf04_circle`, `gaf04_edge`, `gaf04_slim`: for `x = π_j𝓔⁰(p)` with `|η_i(p)| ≤ 7ℓ_i` (edges also
  `t(p) ≤ 7Δ`) and every contributor `π_j𝓔⁰(q)`, `q ∈ Ã_j`: (FD), (FV) `|η_i(q)| < 351ℓ_i/49` and
  the exact marker `v_i(π_j𝓔⁰ q) = R_i` (first half of (FM)). `ℓ_i = 1, Δ, 10⁵Δ`.
The plane half of (FM) (`v_i|L_y = 0` for the actual planes of SGP04 / EGP06 / TCP05 and CFS27) is
not part of this module.
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

/-- Normalizing two blocks of a common radius `R > 0`. -/
theorem dist_block_scale_GAF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R : ℝ}
    (hR : 0 < R) (a b : E) (s t : ℝ) :
    dist (WithLp.toLp 2 ((R * s) • a, R * s)) (WithLp.toLp 2 ((R * t) • b, R * t)) =
      R * dist (WithLp.toLp 2 (s • a, s)) (WithLp.toLp 2 (t • b, t)) := by
  have h : ∀ (u : ℝ) (c : E),
      WithLp.toLp 2 ((R * u) • c, R * u) = R • WithLp.toLp 2 (u • c, u) := by
    intro u c
    rw [← WithLp.toLp_smul, Prod.smul_mk, smul_smul, smul_eq_mul]
  rw [h, h, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]

/-- (FV) from a block distance `< R/50` to a full-marker block `(R u, R)`. -/
theorem fv_of_block_dist_GAF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R ℓ ζ : ℝ}
    (hR : 0 < R) (hℓ : 1 ≤ ℓ) {u v : E} (hu : ‖u‖ ≤ 7 * ℓ)
    (hd : dist (WithLp.toLp 2 ((R * ζ) • v, R * ζ)) (WithLp.toLp 2 ((R * 1) • u, R * 1)) <
      R / 50) :
    49 / 50 < ζ ∧ ‖v‖ < 351 / 49 * ℓ := by
  rw [dist_block_scale_GAF hR, one_smul] at hd
  have hd' : dist (WithLp.toLp 2 (ζ • v, ζ)) (WithLp.toLp 2 (u, (1 : ℝ))) < 1 / 50 :=
    lt_of_mul_lt_mul_left (by linarith) hR.le
  exact norm_coordinate_lt_of_block_near_full_marker hℓ hu hd'

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

section FD

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- **(FD)** of GAF04 for a projected actual cloud: retained markers `ι i` with whole blocks in
`t`, plateau cores covering the cloud; with `Σ ≤ ε/10000`, `b = εc⁻¹`, any contributor whose closed
`80bΣρ` ball meets the `8bΣρ` ball of a full-`i`-marker cloud point is within `R_i/50`. -/
theorem gaf04_fd_projected (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    {I : Type*} (ι : I → CGPMarkerIndex L) (t : Finset (CGPTag L Z))
    (ht : ∀ i, cgpMarkerTag L Z (ι i) ∈ t) (core : I → Set X)
    (hcore : ∀ i, core i ⊆ ball (cgpMarkerCentre L (ι i))
      (cgpMarkerDomain L (ι i) * ρ (cgpMarkerCentre L (ι i))))
    (hplateau : ∀ i p, p ∈ core i → cgpMarkerCutoff L (ι i) p = 1) (cloud : Set X)
    (hcover : ∀ p ∈ cloud, ∃ i, p ∈ core i) {εc σ : ℝ} (hε : 0 < εc) (hσ : 0 ≤ σ)
    (hσε : σ ≤ εc / 10000) {px pu : X} (hpx : px ∈ cloud) (hpu : pu ∈ cloud) (i : I)
    (hfullx : cgpMarker L Z (ι i) (cgpProjMap L Z t px) = ρ (cgpMarkerCentre L (ι i)))
    (hmeet : (closedBall (cgpProjMap L Z t pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
      ball (cgpProjMap L Z t px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty) :
    dist (cgpProjMap L Z t pu) (cgpProjMap L Z t px) < ρ (cgpMarkerCentre L (ι i)) / 50 := by
  obtain ⟨hs, hfull, -, -⟩ :=
    projected_cloud_scale_KA3 L Z hΔ hΛ hsmall ι t ht core hcore hplateau cloud hcover
  exact contributor_dist_lt_fiftieth_of_full_marker (P := cloud)
    (fun z => cgpProjMap L Z t z.1) (fun z => ρ z.1) (fun i => cgpMarker L Z (ι i))
    (fun i => ρ (cgpMarkerCentre L (ι i))) (fun _ => hρ _)
    (fun i => lipschitzWith_cgpMarker L Z (ι i)) (fun z => hfull _ ⟨z.1, z.2, rfl⟩)
    (fun i z hz => hs i z.1 hz) hε hσ hσε ⟨px, hpx⟩ ⟨pu, hpu⟩ i hfullx hmeet

/-- The projection onto all tags is the identity: `π_univ 𝓔⁰ = 𝓔⁰`. -/
theorem cgpProjMap_univ_GAF : cgpProjMap L Z Finset.univ = cgpGlobalMap L Z := by
  funext p
  refine PiLp.ext fun a => ?_
  simp only [cgpProjMap, blockRestrict_apply, Finset.mem_univ, ite_true]

/-- The block of a retained tag of `π_t 𝓔⁰` is controlled by the distance of the images. -/
theorem dist_block_le_projMap_GAF {t : Finset (CGPTag L Z)} {a : CGPTag L Z} (ha : a ∈ t)
    (p q : X) :
    dist (cgpGlobalMap L Z p a) (cgpGlobalMap L Z q a) ≤
      dist (cgpProjMap L Z t p) (cgpProjMap L Z t q) := by
  rw [← cgpProjMap_apply_of_mem L Z ha p, ← cgpProjMap_apply_of_mem L Z ha q]
  exact PiLp.dist_apply_le _ _ a

end FD

section Stages

/-- **GAF04, edge stage** on `π₂𝓔⁰`: for `x = π₂𝓔⁰(p)` with `|η_i(p)| ≤ 7Δ`, `t(p) ≤ 7Δ` and every
contributor `π₂𝓔⁰(q)`, `q ∈ Ã₂`: (FD) `|π₂𝓔⁰q − x| < R_i/50`, (FV) `|η_i(q)| < 351Δ/49` and the
exact marker `v_i(π₂𝓔⁰ q) = R_i`. -/
theorem gaf04_edge (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (i : L.edge.finite_centres.toFinset) {px pu : X}
    (hpxi : px ∈ ball i.1 (100 * Δ * ρ i.1)) (hηx : |L.edge.coord i.1 px| ≤ 7 * Δ)
    (htx : cgpHeight L px ≤ 7 * Δ) (hpu : pu ∈ fc27EdgeSet L 8)
    (hmeet : (closedBall (cgpProjMap L Z (cgpQ2Tags L Z) pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
      ball (cgpProjMap L Z (cgpQ2Tags L Z) px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty) :
    dist (cgpProjMap L Z (cgpQ2Tags L Z) pu) (cgpProjMap L Z (cgpQ2Tags L Z) px) < ρ i.1 / 50 ∧
      |L.edge.coord i.1 pu| < 351 / 49 * Δ ∧
      cgpMarker L Z (.inr (.inr i)) (cgpProjMap L Z (cgpQ2Tags L Z) pu) = ρ i.1 := by
  have hΔ0 : 0 < Δ := by linarith
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hcutx : L.edge.cutoff i.1 px = 1 :=
    L.edge.cutoff_eq_one_of_le hΔ0 hi hpxi (by linarith) (by unfold cgpHeight at htx; linarith)
  have hpx : px ∈ fc27EdgeSet L 8 := ⟨i, hpxi, by linarith, by linarith⟩
  have hfullx : cgpMarker L Z (.inr (.inr i)) (cgpProjMap L Z (cgpQ2Tags L Z) px) = ρ i.1 := by
    rw [cgpMarker_projMap L Z (edge_mem_cgpQ2Tags L Z i)]
    change ρ i.1 * L.edge.cutoff i.1 px = ρ i.1
    rw [hcutx, mul_one]
  have hFD : dist (cgpProjMap L Z (cgpQ2Tags L Z) pu) (cgpProjMap L Z (cgpQ2Tags L Z) px) <
      ρ i.1 / 50 :=
    gaf04_fd_projected L Z hΔ hΛ hsmall
      (fun j : L.edge.finite_centres.toFinset => (.inr (.inr j) : CGPMarkerIndex L))
      (cgpQ2Tags L Z) (fun j => edge_mem_cgpQ2Tags L Z j)
      (fun j => {p | p ∈ ball j.1 (100 * Δ * ρ j.1) ∧ |L.edge.coord j.1 p| ≤ 8 * Δ ∧
        cgpHeight L p ≤ 8 * Δ})
      (fun j p hp => hp.1)
      (fun j p hp => L.edge.cutoff_eq_one_of_le hΔ0 ((Set.Finite.mem_toFinset _).mp j.2) hp.1
        hp.2.1 hp.2.2)
      (fc27EdgeSet L 8) (fun p hp => hp) hε hσ hσε hpx hpu i hfullx hmeet
  -- the edge blocks
  have hblk := dist_block_le_projMap_GAF L Z (edge_mem_cgpQ2Tags L Z i) pu px
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * L.edge.cutoff i.1 pu) •
      planeAxis (L.edge.coord i.1 pu), ρ i.1 * L.edge.cutoff i.1 pu))
      (WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis (L.edge.coord i.1 px), ρ i.1 * 1)) < ρ i.1 / 50 := by
    rw [← hcutx]
    exact lt_of_le_of_lt hblk hFD
  obtain ⟨hζ, hv⟩ := fv_of_block_dist_GAF hri hΔ (by rw [norm_planeAxis]; exact hηx) hblk'
  rw [norm_planeAxis] at hv
  have hcutu_ne : L.edge.cutoff i.1 pu ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdom := cgpMarkerCutoff_ne_zero L hΔ0 (.inr (.inr i)) pu hcutu_ne
  obtain ⟨j, -, -, htu⟩ := hpu
  have hcutu : L.edge.cutoff i.1 pu = 1 :=
    L.edge.cutoff_eq_one_of_le hΔ0 hi (by simpa [cgpMarkerCentre, cgpMarkerDomain] using hdom)
      (by nlinarith [abs_nonneg (L.edge.coord i.1 pu)]) (by unfold cgpHeight at htu; exact htu)
  refine ⟨hFD, hv, ?_⟩
  rw [cgpMarker_projMap L Z (edge_mem_cgpQ2Tags L Z i)]
  change ρ i.1 * L.edge.cutoff i.1 pu = ρ i.1
  rw [hcutu, mul_one]

/-- The LC87 circle cutoff is one where `‖η_j‖ ≤ 8` on the chart domain `B(j, 200ρ(j))`. -/
theorem circle_cutoff_eq_one_of_coord_le_GAF
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (j : L.circle.finite_centres.toFinset) {p : X} (hp : p ∈ ball j.1 (200 * ρ j.1))
    (hη : ‖cgpCoord L.toLocalChartFamily Z (.inl j) p‖ ≤ 8) : L.circle.cutoff j.1 p = 1 := by
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have h := L.circle_cutoff_apply hj p
  simp only [mem_ball.mp hp, ↓reduceIte] at h
  rw [h]
  refine circleCutoffBump_LC87.one_of_mem_closedBall ?_
  rw [mem_closedBall, dist_zero_right]
  exact hη

/-- **GAF04, circle stage** on `𝓔⁰` (first cloud `𝓔⁰(Ã₁)`): for `x = 𝓔⁰(p)` with `‖η_i(p)‖ ≤ 7` on
`B(c_i, 200ρ(c_i))` and every contributor `𝓔⁰(q)`, `q ∈ Ã₁`: (FD) `|𝓔⁰q − x| < R_i/50`, (FV)
`‖η_i(q)‖ < 351/49` and the exact marker `v_i(𝓔⁰ q) = R_i`. -/
theorem gaf04_circle
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (i : L.circle.finite_centres.toFinset) {px pu : X}
    (hpxi : px ∈ ball i.1 (200 * ρ i.1))
    (hηx : ‖cgpCoord L.toLocalChartFamily Z (.inl i) px‖ ≤ 7)
    (hpu : pu ∈ fc04Set L.toLocalChartFamily Z 8)
    (hmeet : (closedBall (cgpGlobalMap L.toLocalChartFamily Z pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
      ball (cgpGlobalMap L.toLocalChartFamily Z px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty) :
    dist (cgpGlobalMap L.toLocalChartFamily Z pu) (cgpGlobalMap L.toLocalChartFamily Z px) <
        ρ i.1 / 50 ∧
      ‖cgpCoord L.toLocalChartFamily Z (.inl i) pu‖ < 351 / 49 ∧
      cgpMarker L.toLocalChartFamily Z (.inl i) (cgpGlobalMap L.toLocalChartFamily Z pu) =
        ρ i.1 := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i.1
  have hF := cgpProjMap_univ_GAF L.toLocalChartFamily Z
  have hcutx : L.circle.cutoff i.1 px = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF L Z i hpxi (by linarith)
  have hpx : px ∈ fc04Set L.toLocalChartFamily Z 8 := ⟨i, hpxi, by linarith⟩
  have hfullx : cgpMarker L.toLocalChartFamily Z (.inl i)
      (cgpGlobalMap L.toLocalChartFamily Z px) = ρ i.1 := by
    change ρ i.1 * L.circle.cutoff i.1 px = ρ i.1
    rw [hcutx, mul_one]
  have hFD : dist (cgpGlobalMap L.toLocalChartFamily Z pu)
      (cgpGlobalMap L.toLocalChartFamily Z px) < ρ i.1 / 50 := by
    have h := gaf04_fd_projected L.toLocalChartFamily Z hΔ hΛ hsmall
      (fun j : L.circle.finite_centres.toFinset => (.inl j : CGPMarkerIndex L.toLocalChartFamily))
      Finset.univ (fun _ => Finset.mem_univ _)
      (fun j => {p | p ∈ ball j.1 (200 * ρ j.1) ∧
        ‖cgpCoord L.toLocalChartFamily Z (.inl j) p‖ ≤ 8})
      (fun j p hp => hp.1)
      (fun j p hp => circle_cutoff_eq_one_of_coord_le_GAF L Z j hp.1 hp.2)
      (fc04Set L.toLocalChartFamily Z 8) (fun p hp => hp) hε hσ hσε hpx hpu i
      (by rw [hF]; exact hfullx) (by rw [hF]; exact hmeet)
    rwa [hF] at h
  have hblk : dist (cgpGlobalMap L.toLocalChartFamily Z pu (.inl i))
      (cgpGlobalMap L.toLocalChartFamily Z px (.inl i)) < ρ i.1 / 50 :=
    lt_of_le_of_lt (PiLp.dist_apply_le _ _ _) hFD
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * L.circle.cutoff i.1 pu) •
      cgpCoord L.toLocalChartFamily Z (.inl i) pu, ρ i.1 * L.circle.cutoff i.1 pu))
      (WithLp.toLp 2 ((ρ i.1 * 1) • cgpCoord L.toLocalChartFamily Z (.inl i) px, ρ i.1 * 1)) <
        ρ i.1 / 50 := by
    rw [← hcutx]
    exact hblk
  obtain ⟨hζ, hv⟩ := fv_of_block_dist_GAF hri le_rfl (by linarith) hblk'
  have hcutu_ne : L.circle.cutoff i.1 pu ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdom := cgpMarkerCutoff_ne_zero L.toLocalChartFamily hΔ0 (.inl i) pu hcutu_ne
  have hcutu : L.circle.cutoff i.1 pu = 1 :=
    circle_cutoff_eq_one_of_coord_le_GAF L Z i hdom (by linarith)
  refine ⟨hFD, by linarith, ?_⟩
  change ρ i.1 * L.circle.cutoff i.1 pu = ρ i.1
  rw [hcutu, mul_one]

/-- **GAF04, slim stage** on `π₃𝓔⁰`: for `x = π₃𝓔⁰(p)` with `|η_i(p)| ≤ 7·10⁵Δ` on
`B(c_i, 10⁶Δρ(c_i))` and every contributor `π₃𝓔⁰(q)`, `q ∈ Ã₃`: (FD), (FV)
`|η_i(q)| < (351/49)·10⁵Δ` and the exact marker `v_i(π₃𝓔⁰ q) = R_i`. -/
theorem gaf04_slim (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) {εc σ : ℝ} (hε : 0 < εc)
    (hσ : 0 ≤ σ) (hσε : σ ≤ εc / 10000) (i : L.slim.finite_centres.toFinset) {px pu : X}
    (hpxi : px ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hηx : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord px| ≤
      7 * 10 ^ 5 * Δ)
    (hpu : pu ∈ fc27SlimSet L 8)
    (hmeet : (closedBall (cgpProjMap L Z (cgpQ3Tags L Z) pu) (80 * εc⁻¹ * (σ * ρ pu)) ∩
      ball (cgpProjMap L Z (cgpQ3Tags L Z) px) (8 * εc⁻¹ * (σ * ρ px))).Nonempty) :
    dist (cgpProjMap L Z (cgpQ3Tags L Z) pu) (cgpProjMap L Z (cgpQ3Tags L Z) px) < ρ i.1 / 50 ∧
      |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord pu| <
        351 / 49 * (10 ^ 5 * Δ) ∧
      cgpMarker L Z (.inr (.inl i)) (cgpProjMap L Z (cgpQ3Tags L Z) pu) = ρ i.1 := by
  have hΔ0 : 0 < Δ := by linarith
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hcut : L.slim.cutoff i.1 = (L.slim.centre i.1 hi).cutoff := slimFamily_cutoff_eq_KA2 L hi
  have hcutx : L.slim.cutoff i.1 px = 1 := by
    rw [hcut]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hpxi (by linarith)
  have hpx : px ∈ fc27SlimSet L 8 := ⟨i, hpxi, by linarith⟩
  have hfullx : cgpMarker L Z (.inr (.inl i)) (cgpProjMap L Z (cgpQ3Tags L Z) px) = ρ i.1 := by
    rw [cgpMarker_projMap L Z (slim_mem_cgpQ3Tags L Z i)]
    change ρ i.1 * L.slim.cutoff i.1 px = ρ i.1
    rw [hcutx, mul_one]
  have hFD : dist (cgpProjMap L Z (cgpQ3Tags L Z) pu) (cgpProjMap L Z (cgpQ3Tags L Z) px) <
      ρ i.1 / 50 :=
    gaf04_fd_projected L Z hΔ hΛ hsmall
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
      (fc27SlimSet L 8) (fun p hp => hp) hε hσ hσε hpx hpu i hfullx hmeet
  have hblk := dist_block_le_projMap_GAF L Z (slim_mem_cgpQ3Tags L Z i) pu px
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * L.slim.cutoff i.1 pu) •
      planeAxis ((L.slim.centre i.1 hi).coord pu), ρ i.1 * L.slim.cutoff i.1 pu))
      (WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis ((L.slim.centre i.1 hi).coord px), ρ i.1 * 1)) <
        ρ i.1 / 50 := by
    rw [← hcutx]
    exact lt_of_le_of_lt hblk hFD
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  obtain ⟨hζ, hv⟩ := fv_of_block_dist_GAF hri hℓ (by rw [norm_planeAxis]; linarith) hblk'
  rw [norm_planeAxis] at hv
  have hcutu_ne : L.slim.cutoff i.1 pu ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdom := cgpMarkerCutoff_ne_zero L hΔ0 (.inr (.inl i)) pu hcutu_ne
  have hdom' : pu ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) := by
    change pu ∈ ball i.1 (1000000 * Δ * ρ i.1) at hdom
    rw [mem_ball] at hdom ⊢
    norm_num at hdom ⊢
    exact hdom
  have hcutu : L.slim.cutoff i.1 pu = 1 := by
    rw [hcut]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hdom' (by nlinarith)
  refine ⟨hFD, hv, ?_⟩
  rw [cgpMarker_projMap L Z (slim_mem_cgpQ3Tags L Z i)]
  change ρ i.1 * L.slim.cutoff i.1 pu = ρ i.1
  rw [hcutu, mul_one]

end Stages

end DifferentialGeometry.Geometry.Collapse
