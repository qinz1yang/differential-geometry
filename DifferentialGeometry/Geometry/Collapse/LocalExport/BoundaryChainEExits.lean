import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGaf02ChainE
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCorollaries

/-!
# BCG03: the exits of the enhanced boundary chain (BAUG-Dd)

Targets A0 (block preservation), A3a, A3b, A3d, A3e, A3f, A3g, A3h, A3i of
`TargetsBoundary-A-v3.lean.txt` on `C : BoundaryGaf02ChainE DP …` WITHOUT premises (the register
block is `C.std`):

* `adjust_keeps_block_V2_BAUGD` (D69-6: an adjustment never moves a block outside its stage tags);
* base-chain helpers `BoundaryGaf02Chain.stage_succ_eq_V2_BAUGD`, `cutoff_mem_Icc_V2_BAUGD`,
  `loc_V2_BAUGD`, `input_error_V2_BAUGD` and the generic step `current_input_generic_BAUGD`;
* on `BoundaryGaf02ChainE`: `stage_smooth_BAUGD` (A3a), `stage_error_lt_BAUGD` (A3b),
  `small_marker_zero_BAUGD`, `prefix_am0_BAUGD` (A3d), `segment_am0_BAUGD` (A3e),
  `scale_pos_BAUGD` (A3f), `keeps_orthogonal_coordinates_BAUGD` (A3g),
  `current_input_tests_BAUGD` (A3h), `continuous_heightRatio_BAUGD` (A3i), `deriv_bound_BAUGD`.
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

/-- **A0 v2 block preservation** (D69-6 "later adjustments keep earlier blocks"): an adjustment of
stage `st` (any smoothing map `a`) never moves an interior block outside the stage tags. -/
theorem adjust_keeps_block_V2_BAUGD (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc
    βc Lmax τ γ δ εr e T V vs ζ Λz θ W g δn n B oM) (st : Fin 3)
    (a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (t : S.IntTag_BAUGA)
    (ht : t ∉ S.stageTagsV2_BAUGD st) :
    (actualSlotsV2_BAUGD S).adjust st a z (Sum.inl t) = z (Sum.inl t) := by
  have hnot : (Sum.inl t : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∉
      (actualSlotsV2_BAUGD S).stageTagsAug st := fun h => ht (Finset.inl_mem_disjSum.mp h)
  have h0 : ∀ y, ((actualSlotsV2_BAUGD S).stageProj st y) (Sum.inl t) = 0 := by
    intro y
    simp only [BoundaryInteriorSlots_BIF.stageProj, blockRestrict_apply, hnot, ite_false]
  have hP := stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st
  simp only [BoundaryInteriorSlots_BIF.adjust, adjustmentMap_apply, hP, PiLp.add_apply,
    PiLp.smul_apply, PiLp.sub_apply, h0, sub_self, smul_zero, add_zero]

section Generic

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}

/-- **The CFS16-type tests at one stage input** `y p` (generic in the slot): off `tsupport ψ_st`
the stage is the identity; on it, `p` is an interior point `q` of the stage core, `x = π_st F_∂(q)`
is a cloud point with `3/5 Σρ(q) ≤ r_x ≤ 5/3 Σρ(q)`, the input lies in the tube
`‖π_st y − x‖ ≤ r_x/2`, `[x, π_st y] ⊆ B(x, r_x)`, and the step is at most `Ξ r_x + ‖π_st y − x‖`. -/
theorem current_input_generic_BAUGD
    (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    {st : Fin 3} {Kj : ℕ} {Ξs cws : ℝ}
    (σ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hsg : 0 < Sg st) (hψ : ∀ z, (actualSlotsV2_BAUGD S).cutoff st z ∈ Icc (0 : ℝ) 1)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (p : W.Carrier)
    (hloc : y ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    {e : ℝ} (he : e ≤ 3 * Sg st / 10)
    (hy : ‖y - S.boundaryOriginalMap p‖ ≤ e * S.rho p) :
    (y ∉ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
        (actualSlotsV2_BAUGD S).adjust st σ.map y = y) ∧
      (y ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore st ∧
          (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloud st ∧
          3 / 5 * (Sg st * S.rho q) ≤ DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ∧
          DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ≤
            5 / 3 * (Sg st * S.rho q) ∧
          ‖(actualSlotsV2_BAUGD S).stageProj st y -
              (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ ≤
            DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) / 2 ∧
          segment ℝ ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
              ((actualSlotsV2_BAUGD S).stageProj st y) ⊆
            ball ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
              (DP.stageRadius st (Sg st)
                ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))) ∧
          ‖(actualSlotsV2_BAUGD S).adjust st σ.map y - y‖ ≤
            Ξs * DP.stageRadius st (Sg st)
                ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) +
              ‖(actualSlotsV2_BAUGD S).stageProj st y -
                (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖) := by
  refine ⟨fun hz => adjust_eq_of_notMem_BAUGD st _ hz, fun hz => ?_⟩
  obtain ⟨q, hq, hcore⟩ := hloc hz
  have hx : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud st := ⟨q, hcore, rfl⟩
  have hr := stageRadius_bounds_V2_BAUGD DP hsg.le hcore
  have hρq : S.rho q.val = S.rho p := by rw [hq]
  have hFq : S.boundaryOriginalMap q.val = S.boundaryOriginalMap p := by rw [hq]
  have hρ := S.rho_pos q.val
  have hwx : ‖(actualSlotsV2_BAUGD S).stageProj st y -
      (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ ≤ e * S.rho q := by
    refine (norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) st _ _).trans ?_
    rw [hFq, hρq]
    exact hy
  have htube : ‖(actualSlotsV2_BAUGD S).stageProj st y -
      (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ ≤
      DP.stageRadius st (Sg st)
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) / 2 := by
    have h3 := mul_le_mul_of_nonneg_right he hρ.le
    have h4 : 3 * Sg st / 10 * S.rho q = 3 / 10 * (Sg st * S.rho q) := by ring
    linarith [hr.1]
  have hrpos : 0 < DP.stageRadius st (Sg st)
      ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) := by
    have : 0 < Sg st * S.rho q := mul_pos hsg hρ
    linarith [hr.1]
  have hz' : ‖(actualSlotsV2_BAUGD S).stageProj st y -
      (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ <
      DP.stageRadius st (Sg st)
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) := by linarith
  refine ⟨q, hq, hcore, hx, hr.1, hr.2, htube, ?_, adjust_sub_le_BAUGD σ hx rfl hz' (hψ _)⟩
  refine (convex_ball _ _).segment_subset (mem_ball_self hrpos) ?_
  rw [mem_ball, dist_eq_norm]
  exact hz'

end Generic

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

/-- Each stage output is the stage adjustment of the previous one. -/
theorem stage_succ_eq_V2_BAUGD (st : Fin 3) (p : W.Carrier) :
    C.stage st.succ p =
      (actualSlotsV2_BAUGD S).adjust st (C.slot st).map (C.stage st.castSucc p) := by
  fin_cases st <;> rfl

include C in
/-- The three slot cutoffs take values in `[0, 1]` (the chain's binding fields). -/
theorem cutoff_mem_Icc_V2_BAUGD (st : Fin 3)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).cutoff st z ∈ Icc (0 : ℝ) 1 := by
  have hB := C.cutoff_bindings
  fin_cases st
  · exact hB.1.2.1 z
  · exact hB.2.1.2.1 z
  · exact hB.2.2.2.1 z

/-- The closed-support localization of `ψ_st` at the chain's own input `g_st`. -/
theorem loc_V2_BAUGD (st : Fin 3) (p : W.Carrier)
    (hp : C.stage st.castSucc p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore st := by
  fin_cases st
  · exact C.interior_of_cutoff_zero_V2_BAUGD hp
  · exact C.interior_of_cutoff_one_V2_BAUGD hp
  · exact C.interior_of_cutoff_two_V2_BAUGD hp

/-- The error of the chain's own input `g_st` (`0, c₀, c₁`) and its tube factor `≤ 3Σ_st/10`. -/
theorem input_error_V2_BAUGD (st : Fin 3) (p : W.Carrier) :
    ‖C.stage st.castSucc p - S.boundaryOriginalMap p‖ ≤ ![0, c 0, c 1] st * S.rho p ∧
      ![0, c 0, c 1] st ≤ 3 * Sg st / 10 := by
  have hN := C.numbers
  fin_cases st
  · refine ⟨?_, ?_⟩
    · change ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ ≤ 0 * S.rho p
      simp
    · change (0 : ℝ) ≤ 3 * Sg 0 / 10
      have := (hN.1 0).2.1
      positivity
  · exact ⟨(C.g₁_error_lt_V2_BAUGD p).le, hN.2.2.2.2.2.1⟩
  · exact ⟨(C.g₂_error_lt_V2_BAUGD p).le, hN.2.2.2.2.2.2.2.2.2.2.1⟩

end BoundaryGaf02Chain

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **A3a** stage smoothness on the WHOLE `W`. -/
theorem stage_smooth_BAUGD :
    ∀ k : Fin 4, ContMDiff W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞ (C.toChain.stage k) := by
  obtain ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, -⟩ := C.std
  exact C.toChain.stage_smooth_V2_BAUGD hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he

/-- **A3b** strict cumulative value errors in the ORIGINAL metric. -/
theorem stage_error_lt_BAUGD :
    ∀ (k : Fin 3) (p : W.Carrier),
      ‖C.toChain.stage k.succ p - S.boundaryOriginalMap p‖ < c k * S.rho p := by
  intro k p
  fin_cases k
  · exact C.toChain.g₁_error_lt_V2_BAUGD p
  · exact C.toChain.g₂_error_lt_V2_BAUGD p
  · exact C.toChain.E_error_lt_V2_BAUGD p

/-- **A3d (ZM)** small markers vanish at every later stage: `ρ(c_m) < ρ(q)/16 ⟹ v_m(g_{k+1} q) = 0`. -/
theorem small_marker_zero_BAUGD :
    ∀ (k : Fin 3) (q : W.pieceInterior ⊤) (m : S.MarkerIdx_BAUGC),
      S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 →
      S.markerCLM_BAUGC m (C.toChain.stage k.succ q.val) = 0 := by
  obtain ⟨hΛ, -, -, -, -, hV, hβ1, hb, -, hΔ1, hLΛ, -⟩ := C.std
  exact fun k q m hm => (C.toChain.markers_V2_BAUGD hΛ hΔ1 hLΛ hV hβ1 hb).1 k q.val m hm

/-- **A3d (AM0)** at every prefix. -/
theorem prefix_am0_BAUGD :
    ∀ (k : Fin 4) (m : S.MarkerIdx_BAUGC) (p : W.pieceInterior ⊤),
      S.intCutoff_BAUGA (S.markerTag_BAUGC m) p = 0 →
      |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
          (Sum.inl (S.markerTag_BAUGC m)) (C.toChain.stage k p.val)| ≤
        S.rho (S.markerCentre_BAUGC m) / 32 := by
  obtain ⟨hΛ, -, -, -, -, hV, hβ1, hb, -, hΔ1, hLΛ, -⟩ := C.std
  intro k m p hp
  have hζ : S.markerCutoffW_BAUGD m p.val = 0 := by
    rw [S.markerCutoffW_val_BAUGD]; exact hp
  exact (C.toChain.markers_V2_BAUGD hΛ hΔ1 hLΛ hV hβ1 hb).2.1 k m p.val hζ

/-- **A3e (AM0)** on the segment `[F_∂ p, E p]`. -/
theorem segment_am0_BAUGD :
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.pieceInterior ⊤),
      S.intCutoff_BAUGA (S.markerTag_BAUGC m) p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p.val) (C.toChain.E p.val),
      |blockMarkerCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
          (Sum.inl (S.markerTag_BAUGC m)) z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  obtain ⟨hΛ, -, -, -, -, hV, hβ1, hb, -, hΔ1, hLΛ, -⟩ := C.std
  intro m p hp
  have hζ : S.markerCutoffW_BAUGD m p.val = 0 := by
    rw [S.markerCutoffW_val_BAUGD]; exact hp
  exact (C.toChain.markers_V2_BAUGD hΛ hΔ1 hLΛ hV hβ1 hb).2.2 m p.val hζ

/-- **A3f** the scale exit with the `c₀` budget: `s = ℓ_ρ(g₁)`, `|s − ρ| < c₀ρ`, `s > 0`. -/
theorem scale_pos_BAUGD :
    ∀ p : W.Carrier, C.toChain.scale p = S.scaleMarker_BIF (C.toChain.g₁ p) ∧
      |C.toChain.scale p - S.rho p| < c 0 * S.rho p ∧ 0 < C.toChain.scale p :=
  fun p => ⟨C.toChain.scale_eq_g₁_V2_BAUGD p, C.toChain.scale_pos_V2_BAUGD p⟩

/-- **A3g** kept orthogonal coordinates. -/
theorem keeps_orthogonal_coordinates_BAUGD (st : Fin 3)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    C.toChain.Ψ st z - z ∈ (actualSlotsV2_BAUGD S).stageQ st :=
  C.toChain.Ψ_sub_mem_stageQ_BIF st z

/-- **A3h the CURRENT-INPUT TESTS** (CFS16 type) at the chain's own input `y = g_st(p)`. -/
theorem current_input_tests_BAUGD :
    ∀ (st : Fin 3) (p : W.Carrier),
      (C.toChain.stage st.castSucc p ∉ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
        C.toChain.stage st.succ p = C.toChain.stage st.castSucc p) ∧
      (C.toChain.stage st.castSucc p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore st ∧
          (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
            (actualSlotsV2_BAUGD S).stageCloud st ∧
          3 / 5 * (Sg st * S.rho q) ≤ DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ∧
          DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ≤
            5 / 3 * (Sg st * S.rho q) ∧
          ‖(actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc p) -
              (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ ≤
            DP.stageRadius st (Sg st)
              ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) / 2 ∧
          segment ℝ ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
              ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc p)) ⊆
            ball ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
              (DP.stageRadius st (Sg st)
                ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))) ∧
          ‖C.toChain.stage st.succ p - C.toChain.stage st.castSucc p‖ ≤
            Ξ st * DP.stageRadius st (Sg st)
                ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) +
              ‖(actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc p) -
                (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖) := by
  intro st p
  have hN := C.toChain.numbers
  have hie := C.toChain.input_error_V2_BAUGD st p
  have hgen := current_input_generic_BAUGD DP (C.toChain.slot st) (hN.1 st).2.1
    (C.toChain.cutoff_mem_Icc_V2_BAUGD st) (C.toChain.stage st.castSucc p) p
    (C.toChain.loc_V2_BAUGD st p) hie.2 hie.1
  rw [C.toChain.stage_succ_eq_V2_BAUGD st p]
  exact hgen

/-- **A3i** the height ratio `T = A/s` is continuous (an accessor of the chain, from A3a and A3f). -/
theorem continuous_heightRatio_BAUGD : Continuous C.toChain.heightRatio := by
  have hE : Continuous C.toChain.E := (C.stage_smooth_BAUGD 3).continuous
  have hh : Continuous C.toChain.height := by
    have h1 : Continuous fun z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
        S.heightCoord_BIF z :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous.comp
        (blockVectorCLM (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
          (Sum.inl S.edgeTag_BAUGA)).continuous
    exact h1.comp hE
  have hs : Continuous C.toChain.scale := (S.scaleMarker_BIF.continuous).comp hE
  exact hh.div hs fun p => (C.scale_pos_BAUGD p).2.2.ne'

include C in
/-- The derivative bound of the original map (the field; BCG01's clause at `bder`). -/
theorem deriv_bound_BAUGD :
    ∀ (p : W.Carrier) (v : TangentSpace W.model p),
      ‖mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ bder * Real.sqrt (g.inner p v v) :=
  C.deriv_bound

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
