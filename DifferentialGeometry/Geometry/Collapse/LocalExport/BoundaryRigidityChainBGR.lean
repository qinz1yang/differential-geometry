import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityContributorBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlot

/-!
# BCG04 on the boundary chain, part 2: A3b's value errors, exact isolation, (BI) (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG04 (B:9132); frozen target E1 of
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt` (with the register clause
`0 ≤ Λ`, `1 ≤ Δ`, `1000000 * Δ * Λ < 1 / 100000` approved by the lead 2026-10-05 13:3x).

* `BoundaryStageSlot_BIF.stage_step_BGR`: one stage of the chain (active: CFS15's output; inactive:
  identity) — `‖Ψ_j z − z‖ ≤ ‖z − F_∂ p‖ + Ξ_jΣ_jρ(p)` and `J_b`-isolation for `ρ(p) > 20r_∂`.
* `BoundaryGaf02Chain.stageCloud_{zero,one,two}_of_tsupport_BGR`: the chain's CFS31 bindings with
  the stage-core inclusion (A0a's `⊇`) put `π_j F_∂ p` into the stage cloud.
* `BoundaryGaf02Chain.chain_steps_BGR`: `‖g_j − F_∂‖ < c_{j−1}ρ` (tube membership at every stage)
  and `ρ > 20r_∂ ⟹ J_b g_j = 0`.
* **`BoundaryGaf02Chain.bcg04_kernel_BGR`**: E1's three clauses on any slot with the stage-core
  inclusion; `bcg04_BI_BGR`: BCG06's (BI)
  premise at
  `C.E` with `ε_∂ = 20c₃r_∂`; `markerPair_eq_chainBoundary_BGR` (review 72 D72-5: physical units).
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

/-- **One stage of the boundary chain** (A3b's value step and BCG04's isolation step): for an
input `z` within `Σ_j ρ(p)` of `F_∂ p`, whose cutoff support localizes `π_j F_∂ p` into the stage
cloud, `‖Ψ_j z − z‖ ≤ ‖z − F_∂ p‖ + Ξ_jΣ_jρ(p)`; if moreover `ρ(p) > 20r_∂` and `J_b z = 0`, then
`J_b(Ψ_j z) = 0` (every window contributor has `J_b y = 0`, `L_y ≤ ker J_b`). -/
theorem stage_step_BGR (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es)
    {st : Fin 3} {Ξs cws : ℝ} (sl : BoundaryStageSlot_BIF D st Kj Ξs (Sg st) cws)
    (hΞ : 0 < Ξs) (hSgΞ : Sg st ≤ Ξs / 10000) (hψ : ∀ z, Φ.cutoff st z ∈ Icc (0 : ℝ) 1)
    {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (i : Fin S.packet.cusp.count)
    (p : W.Carrier) (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : z ∈ tsupport (Φ.cutoff st) →
      Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st)
    (hz : ‖z - S.boundaryOriginalMap p‖ < Sg st * S.rho p) :
    ‖Φ.adjust st sl.map z - z‖ ≤ ‖z - S.boundaryOriginalMap p‖ + Ξs * (Sg st * S.rho p) ∧
      (20 * rd < S.rho p → S.boundaryBlockCLM_BAUGC i z = 0 →
        S.boundaryBlockCLM_BAUGC i (Φ.adjust st sl.map z) = 0) := by
  cases sl with
  | inactive hcore henl =>
    have hid : Φ.adjust st (BoundaryStageSlot_BIF.map (.inactive hcore henl :
        BoundaryStageSlot_BIF D st Kj Ξs (Sg st) cws)) = id := Φ.adjust_id st
    rw [hid]
    refine ⟨?_, fun _ hz0 => hz0⟩
    simp only [id, sub_self, norm_zero]
    have hσl : 0 < Sg st * S.rho p := lt_of_le_of_lt (norm_nonneg _) hz
    positivity
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
    exact Cfs15StageOutput.stage_step_generic_BGR
      (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O (Φ.stageQ st)
      (Φ.stageProj st) (fun v => DFunLike.congr_fun hπ v) (Φ.cutoff st) hψ
      (S.boundaryBlockCLM_BAUGC i) (Φ.orthogonal_stageQ_le_ker_BGR st i) S.scaleMarker_BIF
      (norm_blockMarkerCLM_le _) hSgΞ (fun y hy => D.stageRadius_eq_BGR hc he hs st _ hy) hℓS
      (fun y hy hρ => D.contributor_boundary_zero_BGR hc he hs hrd hprem hΛ hΔ hΛΔ st hy hρ i)
      (S.boundaryOriginalMap p) z hℓx hloc hz

end BoundaryStageSlot_BIF

namespace BoundarySupply

/-- `J_b F_∂ = 0` off the small scales (`ρ ≥ r_∂`). -/
theorem boundaryBlock_original_eq_zero_BGR (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b'
    s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (i : Fin S.packet.cusp.count) {p : W.Carrier} (hp : rd ≤ S.rho p) :
    S.boundaryBlockCLM_BAUGC i (S.boundaryOriginalMap p) = 0 := by
  change S.boundaryOriginalMap p (Sum.inr i) = 0
  rw [BoundarySupplyCore.boundaryOriginalMap_boundary_block,
    S.toBoundarySupplyCore.block_eq_zero_of_le_rho_BGR hrd hprem i hp, map_zero]

end BoundarySupply

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) {Γc Γe Γs ec ee es : ℝ}

/-- `(u_b, v_b) = J_b(C.E)` in physical units is BCG6-K's pair (review 72, D72-5). -/
theorem markerPair_eq_chainBoundary_BGR (i : Fin S.packet.cusp.count) (x : W.Carrier) :
    C.markerPair i x = (chainBoundaryU_BCG6K C.E i x, chainBoundaryV_BCG6K C.E i x) :=
  rfl

include C in
/-- **Stage-`0` localization** (CFS31 binding + the stage-core inclusion A0a): if `F_∂ p` is in the
closed support of `ψ₀`, then `π₀ F_∂ p` is in the circle stage cloud. -/
theorem stageCloud_zero_of_tsupport_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (p : W.Carrier) (h : S.boundaryOriginalMap p ∈ tsupport (Φ.cutoff 0)) :
    Φ.stageProj 0 (S.boundaryOriginalMap p) ∈ Φ.stageCloud 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, j, hj, hd, hη⟩ := C.cutoff_bindings.1.2.2.2.1 p h
  have hj' : j ∈ S.family.circle.finite_centres.toFinset :=
    S.family.circle.finite_centres.mem_toFinset.mpr hj
  have hmem : q ∈ S.markerCore7_BAUGC (Sum.inl ⟨j, hj'⟩) := ⟨hd, by linarith⟩
  exact ⟨q, hcore 0 (Set.mem_iUnion₂.mpr ⟨Sum.inl ⟨j, hj'⟩, rfl, hmem⟩),
    congrArg (fun y => Φ.stageProj 0 (S.boundaryOriginalMap y)) hq⟩

/-- **Stage-`1` localization**: `g₁ p ∈ tsupport ψ₁ ⟹ π₁ F_∂ p` is in the edge stage cloud. -/
theorem stageCloud_one_of_tsupport_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (p : W.Carrier) (h : C.g₁ p ∈ tsupport (Φ.cutoff 1)) :
    Φ.stageProj 1 (S.boundaryOriginalMap p) ∈ Φ.stageCloud 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, j, hj, hd, hη, ht⟩ := C.cutoff_bindings.2.1.2.2.2.1 p h
  have hj' : j ∈ S.family.edgeB.finite_centres.toFinset :=
    S.family.edgeB.finite_centres.mem_toFinset.mpr hj
  have hmem : q ∈ S.markerCore7_BAUGC (Sum.inr (Sum.inr ⟨j, hj'⟩)) := ⟨hd, hη.le, ht.le⟩
  exact ⟨q, hcore 1 (Set.mem_iUnion₂.mpr ⟨Sum.inr (Sum.inr ⟨j, hj'⟩), rfl, hmem⟩),
    congrArg (fun y => Φ.stageProj 1 (S.boundaryOriginalMap y)) hq⟩

/-- **Stage-`2` localization**: `g₂ p ∈ tsupport ψ₂ ⟹ π₂ F_∂ p` is in the slim stage cloud. -/
theorem stageCloud_two_of_tsupport_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (p : W.Carrier) (h : C.g₂ p ∈ tsupport (Φ.cutoff 2)) :
    Φ.stageProj 2 (S.boundaryOriginalMap p) ∈ Φ.stageCloud 2 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, j, hj, hd, hη⟩ := C.cutoff_bindings.2.2.2.2.2.1 p h
  have hj' : j ∈ S.family.slim.finite_centres.toFinset :=
    S.family.slim.finite_centres.mem_toFinset.mpr hj
  have h5 : (10 : ℝ) ^ 5 * Δ = 100000 * Δ := by norm_num
  rw [h5] at hη
  have hmem : q ∈ S.markerCore7_BAUGC (Sum.inr (Sum.inl ⟨j, hj'⟩)) := ⟨hd, hη.le⟩
  exact ⟨q, hcore 2 (Set.mem_iUnion₂.mpr ⟨Sum.inr (Sum.inl ⟨j, hj'⟩), rfl, hmem⟩),
    congrArg (fun y => Φ.stageProj 2 (S.boundaryOriginalMap y)) hq⟩

include C in
/-- **A3b with BCG04's isolation along the chain** (value errors `‖g_j − F_∂‖ < c_jρ` in the
ORIGINAL metric of `H^∂`, tube membership at every stage, and exact isolation `ρ > 20r_∂ ⟹ J_b g_j =
0`). -/
theorem chain_steps_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p ∧
      ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p ∧
      ‖C.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p ∧
      (20 * rd < S.rho p → S.boundaryBlockCLM_BAUGC i (C.g₁ p) = 0 ∧
        S.boundaryBlockCLM_BAUGC i (C.g₂ p) = 0 ∧ S.boundaryBlockCLM_BAUGC i (C.E p) = 0) := by
  obtain ⟨hj, h0, -, -, -, hc01, h1, -, -, -, hc12, h2, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -, -, hSΞ0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -, -, hSΞ1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -, -, hSΞ2, -⟩ := hj 2
  have hψ0 := C.cutoff_bindings.1.2.1
  have hψ1 := C.cutoff_bindings.2.1.2.1
  have hψ2 := C.cutoff_bindings.2.2.2.1
  have hρ := S.rho_pos p
  -- stage 0
  have hz0 : ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < Sg 0 * S.rho p := by
    rw [sub_self, norm_zero]; positivity
  have st0 := (C.slot 0).stage_step_BGR hc he hs hΞ0 hSΞ0 hψ0 hrd hprem hΛ hΔ hΛΔ i p
    (S.boundaryOriginalMap p) (C.stageCloud_zero_of_tsupport_BGR hcore p) hz0
  have hg1 : Φ.adjust 0 (C.slot 0).map (S.boundaryOriginalMap p) = C.g₁ p := rfl
  rw [hg1, sub_self, norm_zero, zero_add] at st0
  have hx0 : 0 < Ξ 0 * Sg 0 := mul_pos hΞ0 hS0
  have hc0 : 0 < c 0 := by linarith only [hx0, h0]
  have he0 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p := by
    have h3 : Ξ 0 * Sg 0 * S.rho p < c 0 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [hx0, h0]) hρ
    have st01 := st0.1
    linarith only [st01, h3]
  -- stage 1
  have hz1 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < Sg 1 * S.rho p := by
    have h3 : c 0 * S.rho p < Sg 1 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [hc01, hS1]) hρ
    linarith only [h3, he0]
  have st1 := (C.slot 1).stage_step_BGR hc he hs hΞ1 hSΞ1 hψ1 hrd hprem hΛ hΔ hΛΔ i p
    (C.g₁ p) (C.stageCloud_one_of_tsupport_BGR hcore p) hz1
  have hg2 : Φ.adjust 1 (C.slot 1).map (C.g₁ p) = C.g₂ p := rfl
  rw [hg2] at st1
  have hΞc0 : 0 ≤ Ξ 1 * c 0 := mul_nonneg hΞ1.le hc0.le
  have hΞS1 : 0 ≤ Ξ 1 * Sg 1 := (mul_pos hΞ1 hS1).le
  have hc1 : c 0 < c 1 := by linarith only [h1, hΞc0, hΞS1, hc0]
  have he1 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C.g₂ p) (C.g₁ p) (S.boundaryOriginalMap p)
    have hb : (2 * c 0 + Ξ 1 * Sg 1) * S.rho p < c 1 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [h1, hΞc0, hΞS1]) hρ
    have st11 := st1.1
    linarith only [htri, st11, he0, hb]
  -- stage 2
  have hz2 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < Sg 2 * S.rho p := by
    have h3 : c 1 * S.rho p < Sg 2 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [hc12, hS2]) hρ
    linarith only [h3, he1]
  have st2 := (C.slot 2).stage_step_BGR hc he hs hΞ2 hSΞ2 hψ2 hrd hprem hΛ hΔ hΛΔ i p
    (C.g₂ p) (C.stageCloud_two_of_tsupport_BGR hcore p) hz2
  have hg3 : Φ.adjust 2 (C.slot 2).map (C.g₂ p) = C.E p := rfl
  rw [hg3] at st2
  have hc1p : 0 < c 1 := lt_trans hc0 hc1
  have hΞc1 : 0 ≤ Ξ 2 * c 1 := mul_nonneg hΞ2.le hc1p.le
  have hΞS2 : 0 ≤ Ξ 2 * Sg 2 := (mul_pos hΞ2 hS2).le
  have he2 : ‖C.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C.E p) (C.g₂ p) (S.boundaryOriginalMap p)
    have hb : (2 * c 1 + Ξ 2 * Sg 2) * S.rho p < c 2 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [h2, hΞc1, hΞS2]) hρ
    have st21 := st2.1
    linarith only [htri, st21, he1, hb]
  refine ⟨he0, he1, he2, fun hρ20 => ?_⟩
  have hJ0 := S.boundaryBlock_original_eq_zero_BGR hrd hprem i (p := p)
    (by linarith only [hρ20, hrd])
  have hJ1 := st0.2 hρ20 hJ0
  have hJ2 := st1.2 hρ20 hJ1
  exact ⟨hJ1, hJ2, st2.2 hρ20 hJ2⟩

include C in
/-- **BCG04 (BI) on the boundary chain, kernel form** (frozen target E1 of
`TargetsBoundary.lean.txt` on any slot `Φ` whose stage cores contain the threshold-`7` marker cores
— A0a's `⊇` — and any augmented data `D` with BAUG-C's plane spec on the three tables; the register
clause `0 ≤ Λ`, `1 ≤ Δ`, `10⁶ΔΛ < 10⁻⁵` approved by the lead 2026-10-05): exact isolation
`ρ(p) > 20r_∂ ⟹ J_b g_j(p) = J_b F_∂(p) = 0`, `|J_b(g_j − F_∂)| < 20c₃r_∂` componentwise everywhere
(`c₃ = c 2`), and on the segment `[F_∂ p, E p]`. -/
theorem bcg04_kernel_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) :
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0)) ∧
    (∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd) ∧
    ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.E p),
      |(augmentedBoundaryCoord_BC7C i z).1 - (S.packet.toBoundaryCollarPacket.block i p).1| <
          20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i z).2 - (S.packet.toBoundaryCollarPacket.block i p).2| <
          20 * c 2 * rd := by
  obtain ⟨hj, h0, -, -, -, -, h1, -, -, -, -, h2, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -⟩ := hj 2
  have hc0 : 0 < c 0 := by
    have := mul_pos hΞ0 hS0
    linarith only [this, h0]
  have hc01 : c 0 ≤ c 1 := by
    have := mul_nonneg hΞ1.le hc0.le
    have := (mul_pos hΞ1 hS1).le
    linarith only [h1, this, hc0, ‹0 ≤ Ξ 1 * c 0›]
  have hc12 : c 1 ≤ c 2 := by
    have := mul_nonneg hΞ2.le (hc0.trans_le hc01).le
    have := (mul_pos hΞ2 hS2).le
    linarith only [h2, this, hc0, hc01, ‹0 ≤ Ξ 2 * c 1›]
  have hc2 : 0 < c 2 := by linarith only [hc0, hc01, hc12]
  have hsteps := fun i p => C.chain_steps_BGR hcore hc he hs hrd hprem hΛ hΔ hΛΔ i p
  have hblock : ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      S.packet.toBoundaryCollarPacket.block i p =
        augmentedBoundaryCoord_BC7C i (S.boundaryOriginalMap p) := fun i p =>
    (S.augmentedBoundaryCoord_boundaryOriginalMap_BIF p i).symm
  -- clause 1
  have cl1 : ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), 20 * rd < S.rho p →
      augmentedBoundaryCoord_BC7C i (C.stage k p) = (0, 0) ∧
        S.packet.toBoundaryCollarPacket.block i p = (0, 0) := by
    intro k i p hρ
    have hρ' : rd ≤ S.rho p := by linarith only [hρ, hrd]
    have hb := S.toBoundarySupplyCore.block_eq_zero_of_le_rho_BGR hrd hprem i hρ'
    have hJ0 := S.boundaryBlock_original_eq_zero_BGR hrd hprem i hρ'
    obtain ⟨hJ1, hJ2, hJ3⟩ := (hsteps i p).2.2.2 hρ
    refine ⟨?_, hb⟩
    fin_cases k
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ0
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ1
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ2
    · exact augmentedBoundaryCoord_eq_zero_BGR hJ3
  -- the stage distances at small scales
  have hdist : ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier), S.rho p ≤ 20 * rd →
      ‖C.stage k p - S.boundaryOriginalMap p‖ < 20 * c 2 * rd := by
    intro k i p hρ
    have hρp := S.rho_pos p
    have hm : c 2 * S.rho p ≤ c 2 * (20 * rd) := mul_le_mul_of_nonneg_left hρ hc2.le
    obtain ⟨he0, he1, he2, -⟩ := hsteps i p
    have hm0 : c 0 * S.rho p ≤ c 2 * S.rho p :=
      mul_le_mul_of_nonneg_right (hc01.trans hc12) hρp.le
    have hm1 : c 1 * S.rho p ≤ c 2 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρp.le
    have hpos : 0 < 20 * c 2 * rd := by positivity
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
  -- clause 2
  have cl2 : ∀ (k : Fin 4) (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.stage k p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd := by
    intro k i p
    have hpos : 0 < 20 * c 2 * rd := by positivity
    by_cases hρ : 20 * rd < S.rho p
    · obtain ⟨h1', h2'⟩ := cl1 k i p hρ
      rw [h1', h2']
      simp only [sub_self, abs_zero]
      exact ⟨hpos, hpos⟩
    · have hd := hdist k i p (not_lt.mp hρ)
      rw [hblock]
      exact ⟨(abs_augmentedBoundaryCoord_fst_sub_le_BGR _ _ i).trans_lt hd,
        (abs_augmentedBoundaryCoord_snd_sub_le_BGR _ _ i).trans_lt hd⟩
  refine ⟨cl1, cl2, fun i p z hz => ?_⟩
  obtain ⟨a, bb, ha, hbb, hab, rfl⟩ := hz
  have h3 := cl2 3 i p
  change |(augmentedBoundaryCoord_BC7C i (C.E p)).1 -
      (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
    |(augmentedBoundaryCoord_BC7C i (C.E p)).2 -
      (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd at h3
  rw [hblock] at h3 ⊢
  have key : ∀ L : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ,
      L (a • S.boundaryOriginalMap p + bb • C.E p) - L (S.boundaryOriginalMap p) =
        bb * (L (C.E p) - L (S.boundaryOriginalMap p)) := by
    intro L
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, show a = 1 - bb by linarith]
    ring
  have hU := key (chainBoundaryUCLM_BCG6K i)
  have hV := key (blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (Sum.inr i))
  have hb1 : bb ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · change |chainBoundaryUCLM_BCG6K i (a • S.boundaryOriginalMap p + bb • C.E p) -
      chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| < 20 * c 2 * rd
    rw [hU, abs_mul, abs_of_nonneg hbb]
    have h31 : |chainBoundaryUCLM_BCG6K i (C.E p) -
        chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| < 20 * c 2 * rd := h3.1
    calc bb * |chainBoundaryUCLM_BCG6K i (C.E p) -
          chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| ≤
          1 * |chainBoundaryUCLM_BCG6K i (C.E p) -
            chainBoundaryUCLM_BCG6K i (S.boundaryOriginalMap p)| :=
          mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
      _ < 20 * c 2 * rd := by rw [one_mul]; exact h31
  · change |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inr i) (a • S.boundaryOriginalMap p + bb • C.E p) -
      blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inr i) (S.boundaryOriginalMap p)| < 20 * c 2 * rd
    rw [hV, abs_mul, abs_of_nonneg hbb]
    have h32 : |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
        (Sum.inr i) (C.E p) - blockMarkerCLM
          (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)
          (S.boundaryOriginalMap p)| < 20 * c 2 * rd := h3.2
    calc bb * |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
          (Sum.inr i) (C.E p) - blockMarkerCLM
            (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)
            (S.boundaryOriginalMap p)| ≤
          1 * |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
            (Sum.inr i) (C.E p) - blockMarkerCLM
              (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inr i)
              (S.boundaryOriginalMap p)| :=
          mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
      _ < 20 * c 2 * rd := by rw [one_mul]; exact h32


include C in
/-- **BCG06's (BI) premise from E1** (review 72 D72-2 form): globally, `|u_b(E) − (P.block b).1| <
ε_∂` and `|v_b(E) − (P.block b).2| < ε_∂` with `ε_∂ = 20c₃r_∂`, against the ACTUAL block
`P.block b` (zero off the band). -/
theorem bcg04_BI_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st)
    (hc : BoundaryEnhancedPlaneSpec D.circle Γc (Sg 0) ec)
    (he : BoundaryEnhancedPlaneSpec D.edge Γe (Sg 1) ee)
    (hs : BoundaryEnhancedPlaneSpec D.slim Γs (Sg 2) es) {rd : ℝ} (hrd : 0 < rd)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (i : Fin S.packet.cusp.count) (p : W.Carrier) :
    |(augmentedBoundaryCoord_BC7C i (C.E p)).1 -
        (S.packet.toBoundaryCollarPacket.block i p).1| < 20 * c 2 * rd ∧
      |(augmentedBoundaryCoord_BC7C i (C.E p)).2 -
        (S.packet.toBoundaryCollarPacket.block i p).2| < 20 * c 2 * rd :=
  (C.bcg04_kernel_BGR hcore hc he hs hrd hprem hΛ hΔ hΛΔ).2.1 3 i p

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse

