import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMarkerChainBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEnhancedPlaneSpecV3

/-!
# BCG04 / BCG05 contributors under spec V3 (slot v2, lead decision (B)) (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG04 (B:9132) and BCG05 (B:9202); frozen targets E1 / E3 of
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt`, rebound to BAUG-D's slot
v2 (`actualSlotsV2_BAUGD`: the scale block is a tag of stage `0` only) and BAUG-C's
`BoundaryEnhancedPlaneSpecV3` (no `scale_kept`; `radius_mcb`, `preimage_comparable`). The stage
radius `Σρ(q̂ x)` is no longer `Σℓ_ρ(x)`; it is COMPARABLE to `Σρ(p)` at an anchor `x = π_j F_∂ p`.

* `Cfs15StageOutput.stage_step_cmp_generic_BGR`: one blend step with comparable anchor radius
  (`3σl/5 ≤ r(x) ≤ 5σl/3`, `‖z − u‖ < 3σl/5`): value bound and level preservation.
* table level, the boundary-slot halves with the spec's `prune_slot` as input:
  `plane_le_ker_boundaryBlock_of_notMem_slot_BGR`, `contributor_boundary_zero_slot_BGR`,
  `pre_band_r_BGR`, `plane_le_ker_marker_of_listed_slot_BGR`,
  `contributor_boundary_marker_slot_BGR`;
* (PRE) / (MCb) read-offs: `rsel_cmp_BGR`, `pre_ge_rsel_BGR`, `radius_window_BGR`;
* **`contributor_zero_window_V3_BGR`** (BCG04: a window contributor of an anchor with
  `ρ > 20r_∂` has `J_b y = 0`, `L_y ≤ ker J_b`; `ρ(pre y) ≥ (27/125)ρ(q) > 3r_∂`) and
  **`contributor_marker_window_V3_BGR`** (BCG05: a window contributor of a `Safe_b` anchor is
  within `r_∂/40`, `v_b y = 1`, `L_y ≤ ker v_b`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Value

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ} {P : H → Submodule ℝ H}

/-- **One active blend step with comparable radii** (slot v2 / spec V3): the anchor radius is
between `3σl/5` and `5σl/3`, `‖z − u‖ < 3σl/5`; then `‖Ψz − z‖ ≤ ‖z − u‖ + ε·5σl/3`, and if the
window contributors all have `J y = c`, `P y ≤ ker J`, `Qᗮ ≤ ker J`, `J z = c`, then `J(Ψz) = c`. -/
theorem _root_.GC.MetricGeometry.Cfs15StageOutput.stage_step_cmp_generic_BGR {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (O : Cfs15StageOutput k K ε cw S T r P)
    (Q : Submodule ℝ H) (pr : H →L[ℝ] H) (hπ : ∀ v, Q.starProjection v = pr v) (ψ : H → ℝ)
    (hψ : ∀ z, ψ z ∈ Icc (0 : ℝ) 1) (J : H →L[ℝ] F')
    (hQJ : Qᗮ ≤ LinearMap.ker (J : H →ₗ[ℝ] F')) {σ l : ℝ} (u z : H) (c : F')
    (hloc : z ∈ tsupport ψ → pr u ∈ S)
    (hrx : z ∈ tsupport ψ → 3 / 5 * (σ * l) ≤ r (pr u) ∧ r (pr u) ≤ 5 / 3 * (σ * l))
    (hz : ‖z - u‖ < 3 / 5 * (σ * l))
    (hcontrib : z ∈ tsupport ψ → ∀ y ∈ O.I,
      (closedBall y (80 * ε⁻¹ * r y) ∩ ball (pr u) (8 * ε⁻¹ * r (pr u))).Nonempty →
        J y = c ∧ P y ≤ LinearMap.ker (J : H →ₗ[ℝ] F')) :
    ‖adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z - z‖ ≤
        ‖z - u‖ + ε * (5 / 3 * (σ * l)) ∧
      (J z = c → J (adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z) = c) := by
  have hε := O.eps_pos
  have hσl : 0 < 3 / 5 * (σ * l) := lt_of_le_of_lt (norm_nonneg _) hz
  by_cases hz0 : z ∈ tsupport ψ
  · have hx := hloc hz0
    obtain ⟨hr1, hr2⟩ := hrx hz0
    have hdist : dist (Q.starProjection z) (pr u) ≤ ‖z - u‖ := by
      rw [dist_eq_norm, ← hπ u, ← map_sub]
      exact Submodule.norm_starProjection_apply_le _ _
    have hw : Q.starProjection z ∈ ball (pr u) (r (pr u)) := by
      rw [mem_ball]
      linarith
    refine ⟨?_, fun hJ => O.adjustment_level_BLOC Q J hQJ ψ (x := pr u) hJ
      fun _ => ⟨hx, hw, hcontrib hz0⟩⟩
    have h := O.adjust_value_le_BGR Q ψ hψ hx hw
    have h2 : ε * r (pr u) ≤ ε * (5 / 3 * (σ * l)) := mul_le_mul_of_nonneg_left hr2 hε.le
    linarith
  · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz0
    have hid : adjustmentMap Q (fun y => Q.starProjection (O.ambient y)) ψ z = z := by
      rw [adjustmentMap_apply, h0, zero_smul, add_zero]
    rw [hid]
    refine ⟨?_, fun hJ => hJ⟩
    simp only [sub_self, norm_zero]
    have h1 : 0 ≤ ε * (5 / 3 * (σ * l)) := mul_nonneg hε.le (by linarith)
    linarith [norm_nonneg (z - u)]

end Value

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryStageReferences_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {st : Fin 3} {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {eta : W.pieceInterior ⊤ → W.pieceInterior ⊤ → E}
  {row : W.pieceInterior ⊤ → Fin S.packet.cusp.count → E →L[ℝ] ℝ}
  (R : BoundaryStageReferences_BIF Φ st E eta row) {Γ sg eg : ℝ}

/-- **An unlisted boundary component annihilates the plane** (BCG04's plane half): if `b` is not
in the whole support list `J_∂(a)` of the reference `a = ref y`, the stored model slot of `b`
vanishes identically and the pruning keeps it, so `L_y ≤ ker J_b`. -/
theorem plane_le_ker_boundaryBlock_of_notMem_slot_BGR
    (hslot : ∀ a v (i : Fin S.packet.cusp.count),
      R.planes.prune a v (Sum.inr i) = v (Sum.inr i))
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    {i : Fin S.packet.cusp.count} (hi : i ∉ S.boundaryList_BIF st (R.planes.ref ⟨y, hy⟩)) :
    R.planes.plane y ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] WithLp 2 (ℝ² × ℝ)) := by
  have ha := R.ref_mem ⟨y, hy⟩
  have hpl : R.planes.plane y = stagePlane_PLN R.planes.model R.planes.prune R.planes.coord
      (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩) :=
    R.planes.plane_of_mem hy
  have hzero : ∀ u, (⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩)) u (Sum.inr i) = 0 := fun u => by
    simp only [Function.comp_apply]
    rw [hslot]
    exact R.model_unlisted _ ha i hi u
  rw [hpl]
  by_cases hd : DifferentiableAt ℝ (⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩))
      (R.planes.coord (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩))
  · exact stagePlane_le_ker_proj_PLN (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      R.planes.model R.planes.prune R.planes.coord _ _ (Sum.inr i) hd
      (Filter.Eventually.of_forall hzero)
  · have h0 := fderiv_zero_of_not_differentiableAt hd
    intro v hv
    obtain ⟨u, hu⟩ := hv
    subst hu
    simp only [ContinuousLinearMap.coe_coe, h0, zero_apply, Submodule.zero_mem]

/-- **BCG04's contributor half** at one cloud point `y` of a stage table: if the model preimage
`q = pre y` has `ρ(q) ≥ 3r_∂` (member premise at `r_∂`, `ΛC_a ≤ 1/2`), then the whole boundary block
of `y` vanishes and `L_y ≤ ker J_b` (the component `b` is not in `J_∂(ref y)`). -/
theorem contributor_boundary_zero_slot_BGR
    (hslot : ∀ a v (i : Fin S.packet.cusp.count),
      R.planes.prune a v (Sum.inr i) = v (Sum.inr i)) {rd : ℝ}
    (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΛC : Λ * stageDomain_BIF Δ st ≤ 1 / 2)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hρ : 3 * rd ≤ S.rho (R.planes.pre ⟨y, hy⟩).val) (i : Fin S.packet.cusp.count) :
    S.boundaryBlockCLM_BAUGC i y = 0 ∧
      R.planes.plane y ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            WithLp 2 (ℝ² × ℝ)) := by
  have hpre := R.pre_spec ⟨y, hy⟩
  refine ⟨?_, R.plane_le_ker_boundaryBlock_of_notMem_slot_BGR hslot hy fun hi => ?_⟩
  · have hy' : y = Φ.stageProj st (S.boundaryOriginalMap (R.planes.pre ⟨y, hy⟩).val) := hpre.1.symm
    have hb := S.toBoundarySupplyCore.block_eq_zero_of_le_rho_BGR hrd hprem i
      (show rd ≤ S.rho (R.planes.pre ⟨y, hy⟩).val by linarith)
    rw [hy']
    change blockRestrict (Φ.stageTagsAug st) (S.boundaryOriginalMap _) (Sum.inr i) = 0
    rw [BoundaryInteriorSlots_BIF.stageTagsAug, blockRestrict_disjSum_inr_BGR,
      BoundarySupplyCore.boundaryOriginalMap_boundary_block, hb, map_zero]
  · have hmeet := (BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b
      (P := S.packet.toBoundaryCollarPacket)).mp hi
    have h2 := S.toBoundarySupplyCore.rho_lt_two_of_meets_BGR hrd hprem hΛ hΛC hmeet
    have h3 := S.toBoundarySupplyCore.rho_le_of_dist_lt_BGR hΛ hΛC hpre.2
    linarith

/-- **BCG05.a, marker division** at a cloud point `y` within `r_∂/100` of `x = π_j F_∂ p`,
`p ∈ Safe_b`: the model preimage `q = pre y` is in the collar band with `31 < η_b(q) < 79`, where
the
marker profile is `1`. -/
theorem pre_band_r_BGR
    {r : ℝ} (hr : r ≤ 1 / 10000) {i : Fin S.packet.cusp.count}
    {p : W.Carrier} (hp : p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hyx : dist y (Φ.stageProj st (S.boundaryOriginalMap p)) < r) :
    (R.planes.pre ⟨y, hy⟩).val ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i ∧
      31 < S.packet.height i (R.planes.pre ⟨y, hy⟩).val ∧
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val < 79 ∧
      boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) = 1 := by
  have hpre := R.pre_spec ⟨y, hy⟩
  -- the coordinates of `y` are the actual block of `q = pre y`
  have hcy : S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val =
      augmentedBoundaryCoord_BC7C i y := by
    have h := congrArg (augmentedBoundaryCoord_BC7C i) hpre.1
    rwa [Φ.augmentedBoundaryCoord_stageProj_BGR, S.augmentedBoundaryCoord_boundaryOriginalMap_BIF]
      at h
  have hcx : augmentedBoundaryCoord_BC7C i (Φ.stageProj st (S.boundaryOriginalMap p)) =
      (S.packet.height i p, 1) := by
    rw [Φ.augmentedBoundaryCoord_stageProj_BGR, S.augmentedBoundaryCoord_boundaryOriginalMap_BIF]
    exact S.packet.toBoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA i hp
  have hd1 := abs_augmentedBoundaryCoord_fst_sub_le_BGR y
    (Φ.stageProj st (S.boundaryOriginalMap p)) i
  have hd2 := abs_augmentedBoundaryCoord_snd_sub_le_BGR y
    (Φ.stageProj st (S.boundaryOriginalMap p)) i
  rw [← dist_eq_norm, ← hcy, hcx] at hd1 hd2
  have hu : |(S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val).1 -
      S.packet.height i p| < r := lt_of_le_of_lt hd1 hyx
  have hv : |(S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val).2 - 1| <
      r := lt_of_le_of_lt hd2 hyx
  have hvpos : 0 < (S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val).2 := by
    have := (abs_lt.mp hv).1
    linarith
  -- `q` is in the collar band
  have hband : (R.planes.pre ⟨y, hy⟩).val ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i := by
    by_contra hnot
    have h0 := S.packet.toBoundaryCollarPacket.block_eq_zero_of_notMem_collarBand_BAUGA i hnot
    rw [h0] at hvpos
    exact lt_irrefl _ hvpos
  have hblk := S.packet.toBoundaryCollarPacket.block_eq_of_mem_collarBand_BAUGA i hband
  rw [hblk, boundaryBlock_fst] at hu
  rw [hblk, boundaryBlock_snd] at hv hvpos
  -- marker division
  have hη0 : 0 ≤ S.packet.height i p := by linarith [hp.2.1]
  have hr1 : r < 1 := by linarith
  have hdivr := marker_division_BLOC hu hv hη0 hp.2.2 hr1
  have hq : S.packet.height i (R.planes.pre ⟨y, hy⟩).val *
      boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) /
      boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) =
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val := mul_div_cancel_right₀ _ hvpos.ne'
  rw [hq] at hdivr
  have hshift := height_shift_lt_BLOC (r := r) (by linarith)
  have hηq := height_band_BLOC hp.2.1 hp.2.2 (hdivr.trans hshift)
  have hχ : boundaryProfile (S.packet.height i (R.planes.pre ⟨y, hy⟩).val) = 1 :=
    boundaryProfile_eq_one ⟨by linarith [hηq.1], by linarith [hηq.2]⟩
  exact ⟨hband, hηq.1, hηq.2, hχ⟩

/-- **The plane of a listed contributor lies in `ker v_b`** when the model height of `q = pre y`
is in `(30, 80)` (the (BM) marker is locally constant `1/R_a` there; the pruning keeps the slot). -/
theorem plane_le_ker_marker_of_listed_slot_BGR
    (hslot : ∀ a v (i : Fin S.packet.cusp.count),
      R.planes.prune a v (Sum.inr i) = v (Sum.inr i))
    {i : Fin S.packet.cusp.count}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hi : i ∈ S.boundaryList_BIF st (R.planes.ref ⟨y, hy⟩))
    (hh : 30 < boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
        (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩))
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) ∧
      boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
        (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩))
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) < 80) :
    R.planes.plane y ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := by
  have ha := R.ref_mem ⟨y, hy⟩
  have hpl : R.planes.plane y = stagePlane_PLN R.planes.model R.planes.prune R.planes.coord
      (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩) := R.planes.plane_of_mem hy
  have hcoord := R.coord_eq _ ha
  have hcont : ContinuousAt (boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
      (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
      (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩)))
      (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) :=
    (hasFDerivAt_boundaryModelHeight_BCG8b _ _ _ _ _).continuousAt
  have hev := hcont.eventually (boundaryProfile_eventuallyEq_one ⟨hh.1, hh.2⟩)
  have hval : ∀ u, ((⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩)) u (Sum.inr i)).snd =
      (S.rho (R.planes.ref ⟨y, hy⟩))⁻¹ * boundaryProfile (boundaryModelHeight_BCG8b
        (S.packet.height i (R.planes.ref ⟨y, hy⟩)) (S.rho (R.planes.ref ⟨y, hy⟩))
        (row (R.planes.ref ⟨y, hy⟩) i) (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩)) u) :=
    fun u => by
      have h1 := (hslot (R.planes.ref ⟨y, hy⟩) (R.planes.model (R.planes.ref ⟨y, hy⟩) u)
        i).trans (R.model_listed _ ha i hi u)
      have h2 := congrArg (fun v : WithLp 2 (ℝ² × ℝ) => v.snd) h1
      refine h2.trans ?_
      simp only [planeBlockEmbed_snd_BAUGA, boundaryModel_BCG8b, Prod.smul_snd, boundaryBlock_snd,
        smul_eq_mul]
  have hloc0 : ∀ᶠ u in 𝓝 (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)),
      ((⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
        R.planes.model (R.planes.ref ⟨y, hy⟩)) u (Sum.inr i)).snd =
        (S.rho (R.planes.ref ⟨y, hy⟩))⁻¹ :=
    hev.mono fun u hu => by rw [hval u, hu, mul_one]
  have hc := congrFun hcoord (R.planes.pre ⟨y, hy⟩)
  have hpl2 : R.planes.plane y = stagePlane_PLN R.planes.model R.planes.prune eta
      (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩) := by
    rw [hpl]
    simp only [stagePlane_PLN, hc]
  rw [hpl2]
  by_cases hd : DifferentiableAt ℝ (⇑(R.planes.prune (R.planes.ref ⟨y, hy⟩)) ∘
      R.planes.model (R.planes.ref ⟨y, hy⟩))
      (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩))
  · exact stagePlane_le_ker_marker_PLN
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      R.planes.model R.planes.prune eta _ _ (Sum.inr i) hd hloc0
  · have h0 := fderiv_zero_of_not_differentiableAt hd
    intro v hv
    obtain ⟨u, hu⟩ := hv
    subst hu
    simp only [ContinuousLinearMap.coe_coe, h0, zero_apply, Submodule.zero_mem]


/-- **BCG05's contributor half** at one cloud point `y` of a stage table (blueprint B:9218–9288):
if `y` is within `r_∂/100` of `x = π_j F_∂ p`, `p ∈ Safe_b`, then (marker division) the model
preimage `q = pre y` has `31 < η_b(q) < 79`, so `v_b(y) = 1`; `b` is in the whole list of
`a = ref y` (`q ∈ D_a`), `R_a < 2r_∂`, (BA) puts the model height `h_b(η_a q)` in `(30, 80)`, the
model marker is locally constant `1/R_a` there and `L_y ≤ ker v_b`. -/
theorem contributor_boundary_marker_slot_BGR
    (hslot : ∀ a v (i : Fin S.packet.cusp.count),
      R.planes.prune a v (Sum.inr i) = v (Sum.inr i))
    (hBA : letI := inducedMetricSpace S.completion.metric
      ∀ a ∈ S.stageCentres_BIF st, ∀ i ∈ S.boundaryList_BIF st a, ∀ y : W.pieceInterior ⊤,
        dist y a < stageDomain_BIF Δ st * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a - row a i (eta a y - eta a a)| < θ)
    (hθ : θ < 1 / 100) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΛC : Λ * stageDomain_BIF Δ st ≤ 1 / 2) {i : Fin S.packet.cusp.count}
    {p : W.Carrier} (hp : p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    {r : ℝ} (hr : r ≤ 1 / 10000)
    (hyx : dist y (Φ.stageProj st (S.boundaryOriginalMap p)) < r) :
    S.boundaryMarkerCLM_BAUGC i y = 1 ∧
      R.planes.plane y ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := by
  let _ := inducedMetricSpace S.completion.metric
  have hpre := R.pre_spec ⟨y, hy⟩
  have ha := R.ref_mem ⟨y, hy⟩
  obtain ⟨hband, hη1, hη2, hχ⟩ := R.pre_band_r_BGR hr hp hy hyx
  have hηq : 31 < S.packet.height i (R.planes.pre ⟨y, hy⟩).val ∧
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val < 79 := ⟨hη1, hη2⟩
  have hblk := S.packet.toBoundaryCollarPacket.block_eq_of_mem_collarBand_BAUGA i hband
  have hcy : S.packet.toBoundaryCollarPacket.block i (R.planes.pre ⟨y, hy⟩).val =
      augmentedBoundaryCoord_BC7C i y := by
    have h := congrArg (augmentedBoundaryCoord_BC7C i) hpre.1
    rwa [Φ.augmentedBoundaryCoord_stageProj_BGR, S.augmentedBoundaryCoord_boundaryOriginalMap_BIF]
      at h
  refine ⟨?_, ?_⟩
  · change (augmentedBoundaryCoord_BC7C i y).2 = 1
    rw [← hcy, hblk, boundaryBlock_snd, hχ]
  -- `i` is listed at `a = ref y`
  have hsupp : (R.planes.pre ⟨y, hy⟩).val ∈ tsupport (S.packet.toBoundaryCollarPacket.block i) := by
    refine subset_tsupport _ (Function.mem_support.mpr fun h0 => ?_)
    have := congrArg Prod.snd h0
    rw [hblk, boundaryBlock_snd, hχ] at this
    exact one_ne_zero this
  have hCpos : 0 < stageDomain_BIF Δ st * S.rho (R.planes.ref ⟨y, hy⟩) :=
    lt_of_le_of_lt dist_nonneg hpre.2
  have hmeet : ∃ x ∈ tsupport (S.packet.toBoundaryCollarPacket.block i),
      riemannianEDistOf g (R.planes.ref ⟨y, hy⟩).val x <
        ENNReal.ofReal (stageDomain_BIF Δ st * S.rho (R.planes.ref ⟨y, hy⟩)) := by
    refine ⟨_, hsupp, ?_⟩
    have h1 := riemannianEDistOf_val_le_completion_BDRY1 W g S.completion.metric
      S.completion.inner_le (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)
    rw [inducedMetricSpace_hmetric S.completion.metric, dist_comm] at h1
    exact lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff hCpos).mpr hpre.2)
  have hi : i ∈ S.boundaryList_BIF st (R.planes.ref ⟨y, hy⟩) :=
    BoundaryCollarPacket.mem_boundarySupportList_iff_edist_BCG8b.mpr hmeet
  have hRa := S.toBoundarySupplyCore.rho_lt_two_of_meets_BGR hrd hprem hΛ hΛC hmeet
  have hRpos := S.rho_pos (R.planes.ref ⟨y, hy⟩).val
  -- (BA) at `q`: the model height is within `R_aθ` of `η_b(q)`
  have hba := hBA _ ha i hi _ hpre.2
  have hθ0 : 0 < θ := lt_of_le_of_lt (abs_nonneg _) hba
  have hmodel : |boundaryModelHeight_BCG8b (S.packet.height i (R.planes.ref ⟨y, hy⟩))
        (S.rho (R.planes.ref ⟨y, hy⟩)) (row (R.planes.ref ⟨y, hy⟩) i)
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.ref ⟨y, hy⟩))
        (eta (R.planes.ref ⟨y, hy⟩) (R.planes.pre ⟨y, hy⟩)) -
      S.packet.height i (R.planes.pre ⟨y, hy⟩).val| <
      S.rho (R.planes.ref ⟨y, hy⟩) * θ := by
    simp only [boundaryModelHeight_BCG8b, map_sub]
    simp only [map_sub] at hba
    exact model_error_lt_BGR hRpos hba
  have hRθ : S.rho (R.planes.ref ⟨y, hy⟩) * θ ≤ 1 := by
    have : S.rho (R.planes.ref ⟨y, hy⟩) * θ ≤ 2 * rd * (1 / 100) :=
      mul_le_mul hRa.le hθ.le hθ0.le (by positivity)
    linarith
  have hh := model_height_band_BLOC hηq.1 hηq.2 hmodel hRθ
  exact R.plane_le_ker_marker_of_listed_slot_BGR hslot hy hi hh


/-- (PRE) at a cloud point: the radius selection and any preimage `q` of `x` have comparable
scales, `3ρ(q)/5 ≤ ρ(q̂ x) ≤ 5ρ(q)/3` (spec V3 `preimage_comparable`). -/
theorem rsel_cmp_BGR (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) (x₀ : W.pieceInterior ⊤)
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hx : x ∈ Φ.stageCloud st)
    {q : W.pieceInterior ⊤} (hq : Φ.stageProj st (S.boundaryOriginalMap q.val) = x) :
    3 / 5 * S.rho q ≤ S.rho (R.planes.rsel x₀ x).val ∧
      S.rho (R.planes.rsel x₀ x).val ≤ 5 / 3 * S.rho q := by
  have hT : x ∈ Φ.stageCloudEnlarged st := Set.image_mono hR.cloud_subset hx
  have hsel := R.rpre_spec ⟨x, hT⟩
  rw [R.planes.rsel_of_mem x₀ hT]
  have h1 := hR.preimage_comparable x hT (R.planes.rpre ⟨x, hT⟩) q hsel hq
  have h2 := hR.preimage_comparable x hT q (R.planes.rpre ⟨x, hT⟩) hq hsel
  constructor <;> linarith

/-- (PRE) at the model preimage: `3ρ(q̂ y)/5 ≤ ρ(pre y)`. -/
theorem pre_ge_rsel_BGR (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) (x₀ : W.pieceInterior ⊤)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st) :
    3 / 5 * S.rho (R.planes.rsel x₀ y).val ≤ S.rho (R.planes.pre ⟨y, hy⟩).val := by
  have h := R.rsel_cmp_BGR hR x₀ hy (R.pre_spec ⟨y, hy⟩).1
  linarith [h.2]

/-- (MCb) on a CFS15 window (spec V3 `radius_mcb`, buffer `L' = 88/Ξ`, `L'Σ ≤ 1/5`): two cloud
points at distance `≤ 88Ξ⁻¹·max(r_x, r_y)` have comparable radii. -/
theorem radius_window_BGR (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg) (x₀ : W.pieceInterior ⊤)
    {Ξs : ℝ} (hΞ : 0 < Ξs) (hsgΞ : sg ≤ Ξs / 10000)
    {x y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ Φ.stageCloud st) (hy : y ∈ Φ.stageCloud st)
    (hd : dist y x ≤ 88 * Ξs⁻¹ * max (sg * S.rho (R.planes.rsel x₀ y).val)
      (sg * S.rho (R.planes.rsel x₀ x).val)) :
    sg * S.rho (R.planes.rsel x₀ x).val / (5 / 3) ≤ sg * S.rho (R.planes.rsel x₀ y).val ∧
      sg * S.rho (R.planes.rsel x₀ y).val ≤ 5 / 3 * (sg * S.rho (R.planes.rsel x₀ x).val) := by
  have hsel : ∀ z ∈ Φ.stageCloudEnlarged st,
      Φ.stageProj st (S.boundaryOriginalMap (R.planes.rsel x₀ z).val) = z := fun z hz => by
    rw [R.planes.rsel_of_mem x₀ hz]
    exact R.rpre_spec ⟨z, hz⟩
  have hL : 0 ≤ 88 * Ξs⁻¹ := by positivity
  have hLs : 88 * Ξs⁻¹ * sg ≤ 1 / 5 := by
    have h1 : Ξs⁻¹ * sg ≤ 1 / 10000 := by
      rw [inv_mul_le_iff₀ hΞ]
      linarith
    nlinarith
  exact hR.radius_mcb (R.planes.rsel x₀) hsel (88 * Ξs⁻¹) hL hLs x
    (Set.image_mono hR.cloud_subset hx) y (Set.image_mono hR.cloud_subset hy) hd

/-- **BCG04's contributor half through (MCb)/(PRE)** (spec V3): a window contributor `y` of the
anchor `x = π_j F_∂ q`, `ρ(q) > 20r_∂`, has `J_b y = 0` and `L_y ≤ ker J_b`
(`ρ(pre y) ≥ (27/125)ρ(q) > 3r_∂`). -/
theorem contributor_zero_window_V3_BGR (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg)
    (x₀ : W.pieceInterior ⊤) {Ξs : ℝ} (hΞ : 0 < Ξs) (hsg : 0 < sg) (hsgΞ : sg ≤ Ξs / 10000)
    {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΛC : Λ * stageDomain_BIF Δ st ≤ 1 / 2)
    {q : W.pieceInterior ⊤} (hρq : 20 * rd < S.rho q)
    {x y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ Φ.stageCloud st) (hqx : Φ.stageProj st (S.boundaryOriginalMap q.val) = x)
    (hy : y ∈ Φ.stageCloud st)
    (hwin : (closedBall y (80 * Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ y).val)) ∩
      ball x (8 * Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ x).val))).Nonempty)
    (i : Fin S.packet.cusp.count) :
    S.boundaryBlockCLM_BAUGC i y = 0 ∧
      R.planes.plane y ≤ LinearMap.ker ((S.boundaryBlockCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            WithLp 2 (ℝ² × ℝ)) := by
  obtain ⟨u, hu1, hu2⟩ := hwin
  have hd : dist y x ≤ 88 * Ξs⁻¹ * max (sg * S.rho (R.planes.rsel x₀ y).val)
      (sg * S.rho (R.planes.rsel x₀ x).val) := by
    have h1 := mem_closedBall.mp hu1
    have h2 := (mem_ball.mp hu2).le
    have h3 := dist_triangle_left y x u
    have hm1 := le_max_left (sg * S.rho (R.planes.rsel x₀ y).val)
      (sg * S.rho (R.planes.rsel x₀ x).val)
    have hm2 := le_max_right (sg * S.rho (R.planes.rsel x₀ y).val)
      (sg * S.rho (R.planes.rsel x₀ x).val)
    have hΞi : 0 ≤ Ξs⁻¹ := (inv_pos.mpr hΞ).le
    nlinarith
  have hrw := R.radius_window_BGR hR x₀ hΞ hsgΞ hx hy hd
  have hcx := R.rsel_cmp_BGR hR x₀ hx hqx
  have hpre := R.pre_ge_rsel_BGR hR x₀ hy
  have hρy : 3 / 5 * S.rho (R.planes.rsel x₀ x).val ≤ S.rho (R.planes.rsel x₀ y).val := by
    have h := hrw.1
    have : sg * S.rho (R.planes.rsel x₀ x).val / (5 / 3) =
        sg * (3 / 5 * S.rho (R.planes.rsel x₀ x).val) := by ring
    rw [this] at h
    exact le_of_mul_le_mul_left h hsg
  refine R.contributor_boundary_zero_slot_BGR hR.prune_slot hrd hprem hΛ hΛC hy ?_ i
  nlinarith

/-- **BCG05's contributor half through (MCb)/(PRE)** (spec V3): a window contributor `y` of the
anchor `x = π_j F_∂ p`, `p ∈ Safe_b`, lies within `r_∂/40` of `x` and has `v_b y = 1`,
`L_y ≤ ker v_b`. -/
theorem contributor_marker_window_V3_BGR (hR : BoundaryEnhancedPlaneSpecV3 R Γ sg eg)
    (hBA : letI := inducedMetricSpace S.completion.metric
      ∀ a ∈ S.stageCentres_BIF st, ∀ i ∈ S.boundaryList_BIF st a, ∀ y : W.pieceInterior ⊤,
        dist y a < stageDomain_BIF Δ st * S.rho a →
        |(S.packet.height i y - S.packet.height i a) / S.rho a - row a i (eta a y - eta a a)| < θ)
    (x₀ : W.pieceInterior ⊤) {Ξs : ℝ} (hΞ : 0 < Ξs) (hsg : 0 < sg) (hsgΞ : sg ≤ Ξs / 10000)
    (hθ : θ < 1 / 100) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΛC : Λ * stageDomain_BIF Δ st ≤ 1 / 2) {i : Fin S.packet.cusp.count}
    {q : W.pieceInterior ⊤} (hp : q.val ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    (hρq : S.rho q < rd)
    {x y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ Φ.stageCloud st) (hqx : Φ.stageProj st (S.boundaryOriginalMap q.val) = x)
    (hy : y ∈ Φ.stageCloud st)
    (hwin : (closedBall y (80 * Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ y).val)) ∩
      ball x (8 * Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ x).val))).Nonempty) :
    S.boundaryMarkerCLM_BAUGC i y = 1 ∧
      R.planes.plane y ≤ LinearMap.ker ((S.boundaryMarkerCLM_BAUGC i :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ] ℝ) := by
  obtain ⟨u, hu1, hu2⟩ := hwin
  have h1 := mem_closedBall.mp hu1
  have h2 := (mem_ball.mp hu2).le
  have h3 := dist_triangle_left y x u
  have hd : dist y x ≤ 88 * Ξs⁻¹ * max (sg * S.rho (R.planes.rsel x₀ y).val)
      (sg * S.rho (R.planes.rsel x₀ x).val) := by
    have hm1 := le_max_left (sg * S.rho (R.planes.rsel x₀ y).val)
      (sg * S.rho (R.planes.rsel x₀ x).val)
    have hm2 := le_max_right (sg * S.rho (R.planes.rsel x₀ y).val)
      (sg * S.rho (R.planes.rsel x₀ x).val)
    have hΞi : 0 ≤ Ξs⁻¹ := (inv_pos.mpr hΞ).le
    nlinarith
  have hrw := (R.radius_window_BGR hR x₀ hΞ hsgΞ hx hy hd).2
  have hcx := (R.rsel_cmp_BGR hR x₀ hx hqx).2
  have ha : Ξs⁻¹ * sg ≤ 1 / 10000 := by
    rw [inv_mul_le_iff₀ hΞ]
    linarith
  have ha0 : 0 ≤ Ξs⁻¹ * sg := by positivity
  have hdist : dist y x < rd / 40 := by
    have hΞi : 0 ≤ Ξs⁻¹ := (inv_pos.mpr hΞ).le
    have hρx0 : 0 ≤ S.rho (R.planes.rsel x₀ x).val := (S.rho_pos _).le
    have s1 : Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ y).val) ≤
        Ξs⁻¹ * (5 / 3 * (sg * S.rho (R.planes.rsel x₀ x).val)) :=
      mul_le_mul_of_nonneg_left hrw hΞi
    have s2 : Ξs⁻¹ * (5 / 3 * (sg * S.rho (R.planes.rsel x₀ x).val)) =
        5 / 3 * ((Ξs⁻¹ * sg) * S.rho (R.planes.rsel x₀ x).val) := by ring
    have s3 : Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ x).val) =
        (Ξs⁻¹ * sg) * S.rho (R.planes.rsel x₀ x).val := by ring
    have s4 : (Ξs⁻¹ * sg) * S.rho (R.planes.rsel x₀ x).val ≤
        1 / 10000 * S.rho (R.planes.rsel x₀ x).val := mul_le_mul_of_nonneg_right ha hρx0
    have e1 : dist y x ≤ 80 * (Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ y).val)) +
        8 * (Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ x).val)) := by
      have e2 : 80 * Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ y).val) =
          80 * (Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ y).val)) := by ring
      have e3 : 8 * Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ x).val) =
          8 * (Ξs⁻¹ * (sg * S.rho (R.planes.rsel x₀ x).val)) := by ring
      linarith
    linarith
  have hyx : dist y (Φ.stageProj st (S.boundaryOriginalMap q.val)) < rd / 40 := hqx ▸ hdist
  exact R.contributor_boundary_marker_slot_BGR hR.prune_slot hBA hθ hrd hrd4 hprem hΛ hΛC hp hy
    (by linarith) hyx

end BoundaryStageReferences_BIF

end DifferentialGeometry.Geometry.Collapse
