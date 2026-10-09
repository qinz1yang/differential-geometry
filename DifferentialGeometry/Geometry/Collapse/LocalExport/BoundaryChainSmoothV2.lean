import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedDataPV3
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainSmooth

/-!
# BCG03: the boundary chain on the v2 slot — value errors and smoothness on the WHOLE `W` (BAUG-D)

A3a v2 (lead decision (B); D72-3 (1)): a chain `C : BoundaryGaf02Chain DP.toBoundaryAugmentedData …`
over augmented data with the V3 plane specs `DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S)
Γ Sg eg` on the ACTUAL v2 slot (closed stage tags: the scale block is a tag of stage `0` only). The
CFS15 radius at a cloud point `x = π_j F_∂(p)` is no longer exactly `Σ_jρ(p)`; the V3 field
`preimage_comparable` gives `3/5 Σ_jρ(p) ≤ r_x ≤ 5/3 Σ_jρ(p)` (closed
`gafCloud_preimage_ratio_two_GAF5`), and the tube membership and the value errors use exactly
GAF01's CHOICE factors (`5/3 Ξ_jΣ_j`, `c_{j−1} ≤ 3Σ_j/10`).

* localization to an INTERIOR stage-core point: `interior_of_cutoff_{zero,one,two}_V2_BAUGD`;
* radius bounds: `stageRadius_bounds_V2_BAUGD`;
* value errors on the chain's own data: `g₁_error_lt_V2_BAUGD`, `g₂_error_lt_V2_BAUGD`,
  `E_error_lt_V2_BAUGD` (`‖g_j − F_∂‖ < c_{j−1}ρ` on all of `W`);
* **`stage_smooth_V2_BAUGD`** (A3a on the v2 slot: `g₀ = F_∂, g₁, g₂, g₃ = C.E` smooth on `W`);
  consumer `contMDiff_E_V2_BAUGD`.
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

/-- **The CFS15 radius at a stage-core point** (v2 slot, V3 specs): for `q ∈ A_j` and
`x = π_j F_∂(q)`, `3/5 Σρ(q) ≤ r_x ≤ 5/3 Σρ(q)` (for `0 ≤ Σ`). -/
theorem stageRadius_bounds_V2_BAUGD {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) {st : Fin 3} {sg : ℝ}
    (hsg : 0 ≤ sg) {q : W.pieceInterior ⊤} (hq : q ∈ (actualSlotsV2_BAUGD S).stageCore st) :
    3 / 5 * (sg * S.rho q) ≤
        DP.stageRadius st sg ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ∧
      DP.stageRadius st sg ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ≤
        5 / 3 * (sg * S.rho q) := by
  have hx : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloudEnlarged st := ⟨q, DP.cloud_subset_BAUGD st hq, rfl⟩
  have hsel := stageSel_spec_BAUGD DP.toBoundaryAugmentedData st _ hx
  have h1 := DP.preimage_comparable_BAUGD st _ hx q _ rfl hsel
  have h2 := DP.preimage_comparable_BAUGD st _ hx _ q hsel rfl
  change 3 / 5 * (sg * S.rho q) ≤ sg * S.rho (DP.stageSel st _) ∧
    sg * S.rho (DP.stageSel st _) ≤ 5 / 3 * (sg * S.rho q)
  constructor <;> nlinarith


/-- **The later stages keep the scale slot** (v2 slot, decision (B)): for `st ≠ 0` the scale tag is
not a stage tag, so `ℓ_ρ(Ψ_st z) = ℓ_ρ(z)` for every smoothing map. -/
theorem scaleMarker_adjust_V2_BAUGD {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM} {st : Fin 3} (hst : st ≠ 0)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.scaleMarker_BIF ((actualSlotsV2_BAUGD S).adjust st a z) = S.scaleMarker_BIF z := by
  have hnot : (Sum.inl S.scaleTag_BAUGA : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∉
      (actualSlotsV2_BAUGD S).stageTagsAug st := by
    intro h
    exact S.scaleTag_notMem_stageTagsV2_BAUGD hst (Finset.inl_mem_disjSum.mp h)
  have h0 : ∀ y, S.scaleMarker_BIF ((actualSlotsV2_BAUGD S).stageProj st y) = 0 := by
    intro y
    simp only [BoundarySupplyCore.scaleMarker_BIF, blockMarkerCLM_apply,
      BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hnot, ite_false]
    rfl
  have hP := stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st
  simp only [BoundaryInteriorSlots_BIF.adjust, adjustmentMap_apply, hP, map_add, map_smul, map_sub,
    h0, sub_self, smul_zero, add_zero]

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

/-- `g₁ = Ψ₀ ∘ F_∂` pointwise on the v2 slot. -/
theorem g₁_apply_V2_BAUGD (p : W.Carrier) :
    C.g₁ p = (actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p) :=
  rfl

/-- `g₂ = Ψ₁ ∘ g₁` pointwise on the v2 slot. -/
theorem g₂_apply_V2_BAUGD (p : W.Carrier) :
    C.g₂ p = (actualSlotsV2_BAUGD S).adjust 1 (C.slot 1).map (C.g₁ p) :=
  rfl

/-- `E = Ψ₂ ∘ g₂` pointwise on the v2 slot. -/
theorem E_apply_V2_BAUGD (p : W.Carrier) :
    C.E p = (actualSlotsV2_BAUGD S).adjust 2 (C.slot 2).map (C.g₂ p) :=
  rfl

include C in
/-- **Localization, stage `0`**: `F_∂ p ∈ tsupport ψ₀ ⟹ p` is an INTERIOR point of `A₀`. -/
theorem interior_of_cutoff_zero_V2_BAUGD {p : W.Carrier}
    (hp : S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 0 := by
  have hB := C.cutoff_bindings
  obtain ⟨q, hq, j, hj, hd, hη⟩ := hB.1.2.2.2.1 p hp
  exact ⟨q, hq, mem_actualSlotsV2_stageCore_circle_BAUGD S hj hd (hη.trans (by norm_num))⟩

/-- **Localization, stage `1`**: `g₁ p ∈ tsupport ψ₁ ⟹ p` is an INTERIOR point of `A₁`. -/
theorem interior_of_cutoff_one_V2_BAUGD {p : W.Carrier}
    (hp : C.g₁ p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 1)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 1 := by
  have hB := C.cutoff_bindings
  rw [g₁_apply_V2_BAUGD] at hp
  obtain ⟨q, hq, j, hj, hd, hη, ht⟩ := hB.2.1.2.2.2.1 p hp
  exact ⟨q, hq, mem_actualSlotsV2_stageCore_edge_BAUGD S hj hd hη.le ht.le⟩

/-- **Localization, stage `2`**: `g₂ p ∈ tsupport ψ₂ ⟹ p` is an INTERIOR point of `A₂`. -/
theorem interior_of_cutoff_two_V2_BAUGD {p : W.Carrier}
    (hp : C.g₂ p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 2)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 2 := by
  have hB := C.cutoff_bindings
  rw [g₂_apply_V2_BAUGD, g₁_apply_V2_BAUGD] at hp
  obtain ⟨q, hq, j, hj, hd, hη⟩ := hB.2.2.2.2.2.1 p hp
  have hη' : |S.slimEta_BIF j q| ≤ 7 * (100000 * Δ) := by
    rw [show (100000 : ℝ) = 10 ^ 5 by norm_num]
    exact hη.le
  exact ⟨q, hq, mem_actualSlotsV2_stageCore_slim_BAUGD S hj hd hη'⟩

/-- **The stage-one value error** `‖g₁ p − F_∂ p‖ < c₀ρ(p)` on all of `W`. -/
theorem g₁_error_lt_V2_BAUGD (p : W.Carrier) :
    ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p := by
  have hN := C.numbers
  have hΞ := (hN.1 0).1
  have hsg := (hN.1 0).2.1
  have hv : 5 / 3 * Ξ 0 * Sg 0 < c 0 := hN.2.1
  have hρ := S.rho_pos p
  have hpos : 0 < Ξ 0 * Sg 0 := mul_pos hΞ hsg
  have hB := C.cutoff_bindings
  rw [g₁_apply_V2_BAUGD]
  by_cases hz : S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0)
  · obtain ⟨q, rfl, hq⟩ := C.interior_of_cutoff_zero_V2_BAUGD hz
    have hx : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 0 := ⟨q, hq, rfl⟩
    have hr := stageRadius_bounds_V2_BAUGD DP hsg.le hq
    have hz' : ‖(actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) -
        (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)‖ <
        DP.stageRadius 0 (Sg 0) ((actualSlotsV2_BAUGD S).stageProj 0
          (S.boundaryOriginalMap q.val)) := by
      rw [sub_self, norm_zero]
      have : 0 < 3 / 5 * (Sg 0 * S.rho q) := by have := S.rho_pos q.val; positivity
      linarith [hr.1]
    have h := adjust_sub_le_BAUGD (C.slot 0) hx rfl hz' (hB.1.2.1 _)
    rw [sub_self, norm_zero, add_zero] at h
    have h2 : Ξ 0 * DP.stageRadius 0 (Sg 0) ((actualSlotsV2_BAUGD S).stageProj 0
        (S.boundaryOriginalMap q.val)) ≤ Ξ 0 * (5 / 3 * (Sg 0 * S.rho q)) :=
      mul_le_mul_of_nonneg_left hr.2 hΞ.le
    calc _ ≤ Ξ 0 * (5 / 3 * (Sg 0 * S.rho q)) := h.trans h2
      _ < c 0 * S.rho q := by nlinarith
  · rw [adjust_eq_of_notMem_BAUGD 0 _ hz, sub_self, norm_zero]
    nlinarith

/-- **The stage-two value error** `‖g₂ p − F_∂ p‖ < c₁ρ(p)` on all of `W`. -/
theorem g₂_error_lt_V2_BAUGD (p : W.Carrier) :
    ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p := by
  have hN := C.numbers
  have hΞ1 := (hN.1 1).1
  have hsg1 := (hN.1 1).2.1
  have hv0 : 5 / 3 * Ξ 0 * Sg 0 < c 0 := hN.2.1
  have hc0s : c 0 ≤ 3 * Sg 1 / 10 := hN.2.2.2.2.2.1
  have hv1 : c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) < c 1 := hN.2.2.2.2.2.2.1
  have hρ := S.rho_pos p
  have hc0 : 0 < c 0 := lt_trans (mul_pos (mul_pos (by norm_num) (hN.1 0).1) (hN.1 0).2.1) hv0
  have he1 := C.g₁_error_lt_V2_BAUGD p
  have hB := C.cutoff_bindings
  have hsplit : C.g₂ p - S.boundaryOriginalMap p =
      ((actualSlotsV2_BAUGD S).adjust 1 (C.slot 1).map (C.g₁ p) - C.g₁ p) +
        (C.g₁ p - S.boundaryOriginalMap p) := by
    rw [g₂_apply_V2_BAUGD]; abel
  rw [hsplit]
  by_cases hz : C.g₁ p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 1)
  · obtain ⟨q, rfl, hq⟩ := C.interior_of_cutoff_one_V2_BAUGD hz
    have hx : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 1 := ⟨q, hq, rfl⟩
    have hr := stageRadius_bounds_V2_BAUGD DP hsg1.le hq
    have hwx := norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) 1 (C.g₁ q.val)
      (S.boundaryOriginalMap q.val)
    have hz' : ‖(actualSlotsV2_BAUGD S).stageProj 1 (C.g₁ q.val) -
        (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)‖ <
        DP.stageRadius 1 (Sg 1) ((actualSlotsV2_BAUGD S).stageProj 1
          (S.boundaryOriginalMap q.val)) := by
      have h3 := mul_le_mul_of_nonneg_right hc0s hρ.le
      have h4 : 3 * Sg 1 / 10 * S.rho q = 3 / 10 * (Sg 1 * S.rho q) := by ring
      have hpos : 0 < Sg 1 * S.rho q := mul_pos hsg1 hρ
      linarith [hr.1]
    have h := adjust_sub_le_BAUGD (C.slot 1) hx rfl hz' (hB.2.1.2.1 _)
    have h2 : Ξ 1 * DP.stageRadius 1 (Sg 1) ((actualSlotsV2_BAUGD S).stageProj 1
        (S.boundaryOriginalMap q.val)) ≤ Ξ 1 * (5 / 3 * (Sg 1 * S.rho q)) :=
      mul_le_mul_of_nonneg_left hr.2 hΞ1.le
    have hgap : 0 < c 1 - 5 / 3 * Ξ 1 * Sg 1 - 2 * c 0 := by
      nlinarith [mul_pos hΞ1 hsg1, mul_pos hΞ1 hc0]
    have hprod := mul_pos hgap hρ
    have hexp : (c 1 - 5 / 3 * Ξ 1 * Sg 1 - 2 * c 0) * S.rho q =
        c 1 * S.rho q - Ξ 1 * (5 / 3 * (Sg 1 * S.rho q)) - 2 * (c 0 * S.rho q) := by ring
    calc _ ≤ ‖(actualSlotsV2_BAUGD S).adjust 1 (C.slot 1).map (C.g₁ q.val) - C.g₁ q.val‖ +
          ‖C.g₁ q.val - S.boundaryOriginalMap q.val‖ := norm_add_le _ _
      _ ≤ Ξ 1 * (5 / 3 * (Sg 1 * S.rho q)) + 2 * ‖C.g₁ q.val - S.boundaryOriginalMap q.val‖ := by
          linarith
      _ < Ξ 1 * (5 / 3 * (Sg 1 * S.rho q)) + 2 * (c 0 * S.rho q) := by linarith
      _ ≤ c 1 * S.rho q := by linarith
  · rw [adjust_eq_of_notMem_BAUGD 1 _ hz, sub_self, zero_add]
    have hle : c 0 ≤ c 1 := by
      nlinarith [mul_pos hΞ1 hsg1, mul_pos hΞ1 hc0]
    exact he1.trans_le (mul_le_mul_of_nonneg_right hle hρ.le)

/-- **The stage-three value error** `‖E p − F_∂ p‖ < c₂ρ(p)` on all of `W`. -/
theorem E_error_lt_V2_BAUGD (p : W.Carrier) :
    ‖C.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p := by
  have hN := C.numbers
  have hΞ2 := (hN.1 2).1
  have hsg2 := (hN.1 2).2.1
  have hv0 : 5 / 3 * Ξ 0 * Sg 0 < c 0 := hN.2.1
  have hv1 : c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) < c 1 := hN.2.2.2.2.2.2.1
  have hc1s : c 1 ≤ 3 * Sg 2 / 10 := hN.2.2.2.2.2.2.2.2.2.2.1
  have hv2 : c 1 + (5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) < c 2 :=
    hN.2.2.2.2.2.2.2.2.2.2.2.1
  have hρ := S.rho_pos p
  have hc0 : 0 < c 0 := lt_trans (mul_pos (mul_pos (by norm_num) (hN.1 0).1) (hN.1 0).2.1) hv0
  have hc1 : 0 < c 1 := by
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) (hN.1 1).1) (hN.1 1).2.1
    nlinarith [mul_pos (hN.1 1).1 hc0]
  have he2 := C.g₂_error_lt_V2_BAUGD p
  have hB := C.cutoff_bindings
  have hsplit : C.E p - S.boundaryOriginalMap p =
      ((actualSlotsV2_BAUGD S).adjust 2 (C.slot 2).map (C.g₂ p) - C.g₂ p) +
        (C.g₂ p - S.boundaryOriginalMap p) := by
    rw [E_apply_V2_BAUGD]; abel
  rw [hsplit]
  by_cases hz : C.g₂ p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 2)
  · obtain ⟨q, rfl, hq⟩ := C.interior_of_cutoff_two_V2_BAUGD hz
    have hx : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud 2 := ⟨q, hq, rfl⟩
    have hr := stageRadius_bounds_V2_BAUGD DP hsg2.le hq
    have hwx := norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) 2 (C.g₂ q.val)
      (S.boundaryOriginalMap q.val)
    have hz' : ‖(actualSlotsV2_BAUGD S).stageProj 2 (C.g₂ q.val) -
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)‖ <
        DP.stageRadius 2 (Sg 2) ((actualSlotsV2_BAUGD S).stageProj 2
          (S.boundaryOriginalMap q.val)) := by
      have h3 := mul_le_mul_of_nonneg_right hc1s hρ.le
      have h4 : 3 * Sg 2 / 10 * S.rho q = 3 / 10 * (Sg 2 * S.rho q) := by ring
      have hpos : 0 < Sg 2 * S.rho q := mul_pos hsg2 hρ
      linarith [hr.1]
    have h := adjust_sub_le_BAUGD (C.slot 2) hx rfl hz' (hB.2.2.2.1 _)
    have h2 : Ξ 2 * DP.stageRadius 2 (Sg 2) ((actualSlotsV2_BAUGD S).stageProj 2
        (S.boundaryOriginalMap q.val)) ≤ Ξ 2 * (5 / 3 * (Sg 2 * S.rho q)) :=
      mul_le_mul_of_nonneg_left hr.2 hΞ2.le
    have hgap : 0 < c 2 - 5 / 3 * Ξ 2 * Sg 2 - 2 * c 1 := by
      nlinarith [mul_pos hΞ2 hsg2, mul_pos hΞ2 hc1]
    have hprod := mul_pos hgap hρ
    have hexp : (c 2 - 5 / 3 * Ξ 2 * Sg 2 - 2 * c 1) * S.rho q =
        c 2 * S.rho q - Ξ 2 * (5 / 3 * (Sg 2 * S.rho q)) - 2 * (c 1 * S.rho q) := by ring
    calc _ ≤ ‖(actualSlotsV2_BAUGD S).adjust 2 (C.slot 2).map (C.g₂ q.val) - C.g₂ q.val‖ +
          ‖C.g₂ q.val - S.boundaryOriginalMap q.val‖ := norm_add_le _ _
      _ ≤ Ξ 2 * (5 / 3 * (Sg 2 * S.rho q)) + 2 * ‖C.g₂ q.val - S.boundaryOriginalMap q.val‖ := by
          linarith
      _ < Ξ 2 * (5 / 3 * (Sg 2 * S.rho q)) + 2 * (c 1 * S.rho q) := by linarith
      _ ≤ c 2 * S.rho q := by linarith
  · rw [adjust_eq_of_notMem_BAUGD 2 _ hz, sub_self, zero_add]
    have hle : c 1 ≤ c 2 := by
      nlinarith [mul_pos hΞ2 hsg2, mul_pos hΞ2 hc1]
    exact he2.trans_le (mul_le_mul_of_nonneg_right hle hρ.le)

/-- **A3a on the v2 slot** (D72-3 (1)): with BAUG-A's smoothness inequalities, `g₀ = F_∂`, `g₁`,
`g₂` and `g₃ = C.E` are smooth on the WHOLE original carrier `W`. -/
theorem stage_smooth_V2_BAUGD (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) :
    ∀ k : Fin 4, ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ (C.stage k) := by
  have hF : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ S.boundaryOriginalMap :=
    S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he
  have hN := C.numbers
  have hB := C.cutoff_bindings
  have h1 : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.g₁ := by
    intro p
    have hΨ : ContDiffAt ℝ ∞ ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map)
        (S.boundaryOriginalMap p) := by
      by_cases hz : S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0)
      · obtain ⟨q, rfl, hq⟩ := C.interior_of_cutoff_zero_V2_BAUGD hz
        have hx : (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloud 0 := ⟨q, hq, rfl⟩
        have hr := stageRadius_bounds_V2_BAUGD DP (hN.1 0).2.1.le hq
        have hz' : ‖(actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val) -
            (actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val)‖ <
            DP.stageRadius 0 (Sg 0) ((actualSlotsV2_BAUGD S).stageProj 0
              (S.boundaryOriginalMap q.val)) := by
          rw [sub_self, norm_zero]
          have : 0 < 3 / 5 * (Sg 0 * S.rho q) := by
            have := S.rho_pos q.val; have := (hN.1 0).2.1; positivity
          linarith [hr.1]
        exact adjust_contDiffAt_BAUGD (C.slot 0) hx rfl hz' hB.1.1.contDiffAt
      · exact adjust_contDiffAt_of_notMem_BAUGD 0 _ hz
    exact hΨ.contMDiffAt.comp p (hF p)
  have h2 : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.g₂ := by
    intro p
    have hΨ : ContDiffAt ℝ ∞ ((actualSlotsV2_BAUGD S).adjust 1 (C.slot 1).map) (C.g₁ p) := by
      by_cases hz : C.g₁ p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 1)
      · obtain ⟨q, rfl, hq⟩ := C.interior_of_cutoff_one_V2_BAUGD hz
        have hx : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloud 1 := ⟨q, hq, rfl⟩
        have hsg1 := (hN.1 1).2.1
        have hr := stageRadius_bounds_V2_BAUGD DP hsg1.le hq
        have hρ := S.rho_pos q.val
        have hc0s : c 0 ≤ 3 * Sg 1 / 10 := hN.2.2.2.2.2.1
        have he1 := C.g₁_error_lt_V2_BAUGD q.val
        have hwx := norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) 1 (C.g₁ q.val)
          (S.boundaryOriginalMap q.val)
        have hz' : ‖(actualSlotsV2_BAUGD S).stageProj 1 (C.g₁ q.val) -
            (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val)‖ <
            DP.stageRadius 1 (Sg 1) ((actualSlotsV2_BAUGD S).stageProj 1
              (S.boundaryOriginalMap q.val)) := by
          have h3 := mul_le_mul_of_nonneg_right hc0s hρ.le
          have h4 : 3 * Sg 1 / 10 * S.rho q = 3 / 10 * (Sg 1 * S.rho q) := by ring
          have hpos : 0 < Sg 1 * S.rho q := mul_pos hsg1 hρ
          linarith [hr.1]
        have hscale := (hB.2.1.2.2.2.2 q.val 1 ⟨zero_le_one, le_rfl⟩).1
        rw [sub_self, zero_smul, zero_add, one_smul] at hscale
        have hopen : IsOpen {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) |
            0 < S.scaleMarker_BIF z} :=
          isOpen_lt continuous_const S.scaleMarker_BIF.continuous
        exact adjust_contDiffAt_BAUGD (C.slot 1) hx rfl hz'
          (hB.2.1.1.contDiffAt (hopen.mem_nhds hscale))
      · exact adjust_contDiffAt_of_notMem_BAUGD 1 _ hz
    exact hΨ.contMDiffAt.comp p (h1 p)
  have h3 : ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.E := by
    intro p
    have hΨ : ContDiffAt ℝ ∞ ((actualSlotsV2_BAUGD S).adjust 2 (C.slot 2).map) (C.g₂ p) := by
      by_cases hz : C.g₂ p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 2)
      · obtain ⟨q, rfl, hq⟩ := C.interior_of_cutoff_two_V2_BAUGD hz
        have hx : (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloud 2 := ⟨q, hq, rfl⟩
        have hsg2 := (hN.1 2).2.1
        have hr := stageRadius_bounds_V2_BAUGD DP hsg2.le hq
        have hρ := S.rho_pos q.val
        have hc1s : c 1 ≤ 3 * Sg 2 / 10 := hN.2.2.2.2.2.2.2.2.2.2.1
        have he2 := C.g₂_error_lt_V2_BAUGD q.val
        have hwx := norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) 2 (C.g₂ q.val)
          (S.boundaryOriginalMap q.val)
        have hz' : ‖(actualSlotsV2_BAUGD S).stageProj 2 (C.g₂ q.val) -
            (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)‖ <
            DP.stageRadius 2 (Sg 2) ((actualSlotsV2_BAUGD S).stageProj 2
              (S.boundaryOriginalMap q.val)) := by
          have h3 := mul_le_mul_of_nonneg_right hc1s hρ.le
          have h4 : 3 * Sg 2 / 10 * S.rho q = 3 / 10 * (Sg 2 * S.rho q) := by ring
          have hpos : 0 < Sg 2 * S.rho q := mul_pos hsg2 hρ
          linarith [hr.1]
        exact adjust_contDiffAt_BAUGD (C.slot 2) hx rfl hz' hB.2.2.1.contDiffAt
      · exact adjust_contDiffAt_of_notMem_BAUGD 2 _ hz
    exact hΨ.contMDiffAt.comp p (h2 p)
  intro k
  fin_cases k
  · exact hF
  · exact h1
  · exact h2
  · exact h3

/-- **Consumer** (BCG6-K's input on the v2 slot): `C.E` is smooth on the whole original carrier. -/
theorem contMDiff_E_V2_BAUGD (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) :
    ContMDiff W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ C.E :=
  C.stage_smooth_V2_BAUGD hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he 3

/-- **The scale is the first blend's** (v2 slot): `s = ℓ_ρ(E) = ℓ_ρ(g₁)`. -/
theorem scale_eq_g₁_V2_BAUGD (p : W.Carrier) : C.scale p = S.scaleMarker_BIF (C.g₁ p) := by
  change S.scaleMarker_BIF (C.E p) = _
  rw [E_apply_V2_BAUGD, scaleMarker_adjust_V2_BAUGD (by decide), g₂_apply_V2_BAUGD,
    scaleMarker_adjust_V2_BAUGD (by decide)]

/-- **A3f (`c₀` budget, decision (B))**: `|s − ρ| < c₀ρ` and `s > 0` on all of `W`. -/
theorem scale_pos_V2_BAUGD (p : W.Carrier) :
    |C.scale p - S.rho p| < c 0 * S.rho p ∧ 0 < C.scale p := by
  have hN := C.numbers
  have hc512 : c 0 ≤ 1 / 512 := hN.2.2.1
  have he1 := C.g₁_error_lt_V2_BAUGD p
  have hρ := S.rho_pos p
  have h1 : C.scale p - S.rho p = S.scaleMarker_BIF (C.g₁ p - S.boundaryOriginalMap p) := by
    rw [C.scale_eq_g₁_V2_BAUGD, map_sub, S.scaleMarker_boundaryOriginalMap_BIF]
  have h2 : |C.scale p - S.rho p| ≤ ‖C.g₁ p - S.boundaryOriginalMap p‖ := by
    rw [h1]
    exact abs_blockMarkerCLM_le_BAUGC (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
      _ _
  have h3 := h2.trans_lt he1
  refine ⟨h3, ?_⟩
  have h4 := (abs_lt.mp h3).1
  have h5 : c 0 * S.rho p ≤ 1 / 512 * S.rho p := mul_le_mul_of_nonneg_right hc512 hρ.le
  linarith

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
