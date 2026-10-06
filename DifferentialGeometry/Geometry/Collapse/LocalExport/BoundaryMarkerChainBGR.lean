import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryMarkerContributorBGR

/-!
# BCG05 on the boundary chain, part 2: (BFM) and E1's whole-block exit (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG05 (B:9202) and BCG04 (B:9132); frozen targets E3 and E1 of
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt` (register clause and
`θ < 1 / 100` approved by the lead 2026-10-05; review 69 D69-8).

* `BoundaryStageSlot_BIF.stage_marker_BGR`: one stage keeps `v_b = 1` (every window contributor).
* **`BoundaryGaf02Chain.bcg05_kernel_BGR`**: E3 — on `Safe_b`, `v_b(g_j p) = 1` for `j = 0, …, 3`,
on any
  slot with the stage-core inclusion; `bcg05_BFM_BGR`: BCG06's (BFM) premise at `C.E`.
* **`BoundaryGaf02Chain.bcg04_block_norm_BGR`**: E1's whole-block exit `‖J_b(g_j − F_∂)‖ < 20c₃r_∂`
  (D69-8; the scalar estimates of `bcg04_kernel_BGR` are its coordinates).
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
variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryStageSlot_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Γc Γe Γs ec ee es : ℝ} {Sg : Fin 3 → ℝ} {Kj : ℕ}

/-- **One stage keeps the boundary marker** (BCG05 at one stage, blueprint B:9218–9288): for
`p ∈ Safe_b` and an input `z` within `Σ_jρ(p)` of `F_∂ p` whose cutoff support localizes
`π_j F_∂ p` into the cloud, `v_b z = 1 ⟹ v_b(Ψ_j z) = 1` — EVERY window contributor has
`v_b y = 1` and `L_y ≤ ker v_b`. -/
theorem stage_marker_BGR (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) (hθ : θ < 1 / 100)
    {st : Fin 3} {Ξs cws : ℝ} (sl : BoundaryStageSlot_BIF D st Kj Ξs (Sg st) cws)
    (hSgΞ : Sg st ≤ Ξs / 10000) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) {i : Fin S.packet.cusp.count}
    {p : W.Carrier} (hp : p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : z ∈ tsupport (Φ.cutoff st) →
      Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st)
    (hz : ‖z - S.boundaryOriginalMap p‖ < Sg st * S.rho p)
    (hz1 : S.boundaryMarkerCLM_BAUGC i z = 1) :
    S.boundaryMarkerCLM_BAUGC i (Φ.adjust st sl.map z) = 1 := by
  cases sl with
  | inactive hcore henl =>
    have hid : Φ.adjust st (BoundaryStageSlot_BIF.map (.inactive hcore henl :
        BoundaryStageSlot_BIF D st Kj Ξs (Sg st) cws)) = id := Φ.adjust_id st
    rw [hid]
    exact hz1
  | active O =>
    have hmap : Φ.adjust st (BoundaryStageSlot_BIF.map (.active O :
        BoundaryStageSlot_BIF D st Kj Ξs (Sg st) cws)) =
        adjustmentMap (Φ.stageQ st) (fun y => (Φ.stageQ st).starProjection (O.ambient y))
          (Φ.cutoff st) := rfl
    rw [hmap]
    have hπ := Φ.starProjection_stageQ_BGR st
    have hℓx : S.scaleMarker_BIF (Φ.stageProj st (S.boundaryOriginalMap p)) = S.rho p := by
      rw [Φ.scaleMarker_stageProj_BGR (D.scale_kept_BGR hc he hs st)]
      exact S.scaleMarker_boundaryOriginalMap_BIF p
    have hℓS : ∀ y ∈ Φ.stageCloud st, 0 ≤ S.scaleMarker_BIF y := fun y hy => by
      have h1 := D.stageRadius_eq_BGR hc he hs st 1 hy
      unfold BoundaryAugmentedData.stageRadius at h1
      rw [one_mul, one_mul] at h1
      rw [← h1]
      exact (S.rho_pos _).le
    have hℓlip : ∀ x ∈ Φ.stageCloud st, ∀ y ∈ Φ.stageCloud st,
        |S.scaleMarker_BIF y - S.scaleMarker_BIF x| ≤ dist y x := fun x _ y _ => by
      rw [← map_sub, dist_eq_norm, ← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (norm_blockMarkerCLM_le _))
    have hne : S.packet.toBoundaryCollarPacket.block i p ≠ 0 := fun h0 => by
      have h1 := S.packet.toBoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA i hp
      rw [h0] at h1
      exact zero_ne_one (congrArg Prod.snd h1)
    have hρp : S.rho p < rd := S.toBoundarySupplyCore.rho_lt_of_mem_tsupport_block_BGR hrd hprem
      (i := i) (subset_tsupport (S.packet.toBoundaryCollarPacket.block i)
        (Function.mem_support.mpr hne))
    exact Cfs15StageOutput.stage_marker_generic_BGR
      (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O (Φ.stageQ st)
      (Φ.stageProj st) (fun v => DFunLike.congr_fun hπ v) (Φ.cutoff st)
      (S.boundaryMarkerCLM_BAUGC i) (Φ.orthogonal_stageQ_le_ker_marker_BGR st i)
      (fun y => S.scaleMarker_BIF y) hℓlip hℓS hSgΞ
      (fun y hy => D.stageRadius_eq_BGR hc he hs st _ hy) (S.boundaryOriginalMap p) z hℓx hloc hz
      (fun y hy hd => D.contributor_boundary_marker_BGR hc he hs hθ hrd hrd4 hprem hΛ hΔ hΛΔ st hp
        hy (by linarith)) hz1

end BoundaryStageSlot_BIF

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) {Γc Γe Γs ec ee es : ℝ}

include C in
/-- **BCG05 (BFM) on the boundary chain, kernel form** (frozen target E3, register clause and
`θ < 1/100` approved 2026-10-05): on `Safe_b` the boundary marker of EVERY stage output is exactly
`1` — `v_b(g_j p) = 1`, `j = 0, …, 3` (every window contributor of every active stage has
`v_b = 1` and `L_y ≤ ker v_b`). -/
theorem bcg05_kernel_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) (hθ : θ < 1 / 100) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.stage k p)).2 = 1 := by
  intro k i p hp
  obtain ⟨hj, -, -, -, -, hc01, -, -, -, -, hc12, -, -, -⟩ := C.numbers
  obtain ⟨-, hS0, -, -, hSΞ0, -⟩ := hj 0
  obtain ⟨-, hS1, -, -, hSΞ1, -⟩ := hj 1
  obtain ⟨-, hS2, -, -, hSΞ2, -⟩ := hj 2
  have hψ0 := C.cutoff_bindings.1.2.1
  have hψ1 := C.cutoff_bindings.2.1.2.1
  have hψ2 := C.cutoff_bindings.2.2.2.1
  have hρ := S.rho_pos p
  obtain ⟨he0, he1, -, -⟩ := C.chain_steps_BGR hcore hc he hs hrd hprem hΛ hΔ hΛΔ i p
  have hz0 : ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < Sg 0 * S.rho p := by
    rw [sub_self, norm_zero]; positivity
  have hz1 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < Sg 1 * S.rho p := by
    have h3 : c 0 * S.rho p < Sg 1 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [hc01, hS1]) hρ
    linarith only [h3, he0]
  have hz2 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < Sg 2 * S.rho p := by
    have h3 : c 1 * S.rho p < Sg 2 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [hc12, hS2]) hρ
    linarith only [h3, he1]
  have hv0 : S.boundaryMarkerCLM_BAUGC i (S.boundaryOriginalMap p) = 1 := by
    change (S.boundaryOriginalMap p (Sum.inr i)).snd = 1
    rw [BoundarySupplyCore.boundaryOriginalMap_boundary_block, planeBlockEmbed_snd_BAUGA,
      S.packet.toBoundaryCollarPacket.block_eq_of_mem_safeBand_BAUGA i hp]
  have hv1 : S.boundaryMarkerCLM_BAUGC i (C.g₁ p) = 1 :=
    (C.slot 0).stage_marker_BGR hc he hs hθ hSΞ0 hrd hrd4 hprem hΛ hΔ hΛΔ hp
      (S.boundaryOriginalMap p) (C.stageCloud_zero_of_tsupport_BGR hcore p) hz0 hv0
  have hv2 : S.boundaryMarkerCLM_BAUGC i (C.g₂ p) = 1 :=
    (C.slot 1).stage_marker_BGR hc he hs hθ hSΞ1 hrd hrd4 hprem hΛ hΔ hΛΔ hp
      (C.g₁ p) (C.stageCloud_one_of_tsupport_BGR hcore p) hz1 hv1
  have hv3 : S.boundaryMarkerCLM_BAUGC i (C.E p) = 1 :=
    (C.slot 2).stage_marker_BGR hc he hs hθ hSΞ2 hrd hrd4 hprem hΛ hΔ hΛΔ hp
      (C.g₂ p) (C.stageCloud_two_of_tsupport_BGR hcore p) hz2 hv2
  fin_cases k
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3

include C in
/-- **BCG06's (BFM) premise from E3**: `v_b(C.E) = 1` on `Safe_b`. -/
theorem bcg05_BFM_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) (hθ : θ < 1 / 100) {rd : ℝ}
    (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (i : Fin S.packet.cusp.count) :
    ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
      (augmentedBoundaryCoord_BC7C i (C.E p)).2 = 1 :=
  C.bcg05_kernel_BGR hcore hc he hs hθ hrd hrd4 hprem hΛ hΔ hΛΔ 3 i

include C in
/-- **E1's whole-block exit** (review 69 D69-8): `‖J_b(g_j − F_∂)‖ < ε_∂ = 20c₃r_∂` for the WHOLE
physical block (the two scalar estimates of `bcg04_kernel_BGR` follow from it). -/
theorem bcg04_block_norm_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ‖S.boundaryBlockCLM_BAUGC i (C.stage k p - S.boundaryOriginalMap p)‖ < 20 * c 2 * rd := by
  intro k i p
  obtain ⟨hj, h0, -, -, -, -, h1, -, -, -, -, h2, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -⟩ := hj 2
  have hc0 : 0 < c 0 := by
    have := mul_pos hΞ0 hS0
    linarith only [this, h0]
  have hc01 : c 0 ≤ c 1 := by
    have h3 := mul_nonneg hΞ1.le hc0.le
    have h4 := (mul_pos hΞ1 hS1).le
    linarith only [h1, h3, h4, hc0]
  have hc12 : c 1 ≤ c 2 := by
    have h3 := mul_nonneg hΞ2.le (hc0.trans_le hc01).le
    have h4 := (mul_pos hΞ2 hS2).le
    linarith only [h2, h3, h4, hc0, hc01]
  have hc2 : 0 < c 2 := by linarith only [hc0, hc01, hc12]
  have hpos : 0 < 20 * c 2 * rd := by positivity
  have hρp := S.rho_pos p
  obtain ⟨he0, he1, he2, hiso⟩ := C.chain_steps_BGR hcore hc he hs hrd hprem hΛ hΔ hΛΔ i p
  by_cases hρ : 20 * rd < S.rho p
  · have hJ0 := S.boundaryBlock_original_eq_zero_BGR hrd hprem i (p := p)
      (by linarith only [hρ, hrd])
    obtain ⟨hJ1, hJ2, hJ3⟩ := hiso hρ
    have hk : S.boundaryBlockCLM_BAUGC i (C.stage k p) = 0 := by
      fin_cases k
      · exact hJ0
      · exact hJ1
      · exact hJ2
      · exact hJ3
    rw [map_sub, hk, hJ0, sub_zero, norm_zero]
    exact hpos
  · have hle : S.rho p ≤ 20 * rd := not_lt.mp hρ
    have hm : c 2 * S.rho p ≤ c 2 * (20 * rd) := mul_le_mul_of_nonneg_left hle hc2.le
    have hm0 : c 0 * S.rho p ≤ c 2 * S.rho p :=
      mul_le_mul_of_nonneg_right (hc01.trans hc12) hρp.le
    have hm1 : c 1 * S.rho p ≤ c 2 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρp.le
    have hd : ‖C.stage k p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd := by
      fin_cases k
      · change ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        rw [sub_self, norm_zero]
        exact hpos
      · change ‖C.g₁ p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        linarith only [he0, hm0, hm]
      · change ‖C.g₂ p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        linarith only [he1, hm1, hm]
      · change ‖C.E p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd
        linarith only [he2, hm]
    have hn := PiLp.norm_apply_le (C.stage k p - S.boundaryOriginalMap p) (Sum.inr i)
    exact lt_of_le_of_lt hn hd

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse

