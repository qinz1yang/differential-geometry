import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainMarkersChain
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainChoiceV2

/-!
# BCG03: assembly of the boundary chain from its three slots (BAUG-Dd)

Part (c) of target A2-mk (`TargetsBoundary-A-v3.lean.txt`; review 69 D69-5): the chain's cutoff
bindings are FIELDS, so the chain is built in two passes through its slots — the raw stage outputs
`g₁ = Ψ₀ ∘ F_∂`, `g₂ = Ψ₁ ∘ g₁` written through the slots, their errors, their (ZM) inputs, then
BAUG-PSI's bindings of `ψ₁`, `ψ₂` at these maps (closed template `gaf02_chainE_mk_GAF8`).

* `step_error_raw_BAUGD`: one stage step `‖Ψ_st(y p) − F_∂ p‖ ≤ (5/3 Ξ Σ + 2e)ρ(p)` for any slot,
  from the closed-support localization of `ψ_st` at `y` and `‖y − F_∂‖ ≤ eρ`, `e ≤ 3Σ/10`;
* **`exists_chain_of_slots_BAUGD`**: for every supply with the six register inequalities of the
  bindings, every `DP` over the actual v2 slot, every three slots `σ` and the CHOICE's `numbers`
  clause at `(b_cut, b_der, κ = cutoffKappa_BAUGP2)` with `b_cut ≥ b₀, b₁, b₂`: a chain with
  `C.slot = σ` (ψ₀ by BAUG-D G4, ψ₁ / ψ₂ by BAUG-PSI with the (ZM) inputs of G6).
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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}

/-- **One raw stage step**: for any slot of stage `st`, an input `y` with `‖y − F_∂‖ ≤ eρ`
(`e ≤ 3Σ/10`) and the closed-support localization of `ψ_st` at `y` into the stage core,
`‖Ψ_st(y p) − F_∂ p‖ ≤ (5/3 Ξ Σ + 2e)ρ(p)` on all of `W`. -/
theorem step_error_raw_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    {st : Fin 3} {Kj : ℕ} {Ξs cws : ℝ}
    (σ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hΞ : 0 ≤ Ξs) (hsg : 0 < Sg st)
    (hψ : ∀ z, (actualSlotsV2_BAUGD S).cutoff st z ∈ Icc (0 : ℝ) 1)
    (y : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : ∀ p : W.Carrier, y p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 3 * Sg st / 10)
    (hy : ∀ p : W.Carrier, ‖y p - S.boundaryOriginalMap p‖ ≤ e * S.rho p) (p : W.Carrier) :
    ‖(actualSlotsV2_BAUGD S).adjust st σ.map (y p) - S.boundaryOriginalMap p‖ ≤
      (5 / 3 * Ξs * Sg st + 2 * e) * S.rho p := by
  have hρ := S.rho_pos p
  have hyp := hy p
  by_cases hz : y p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st)
  · obtain ⟨q, hq, hcore⟩ := hloc p hz
    have hx : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
        (actualSlotsV2_BAUGD S).stageCloud st := ⟨q, hcore, rfl⟩
    have hr := stageRadius_bounds_V2_BAUGD DP hsg.le hcore
    have hρq : S.rho q.val = S.rho p := by rw [hq]
    have hFq : S.boundaryOriginalMap q.val = S.boundaryOriginalMap p := by rw [hq]
    have hwx : ‖(actualSlotsV2_BAUGD S).stageProj st (y p) -
        (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ ≤ e * S.rho p := by
      refine (norm_stageProj_sub_le_BAUGD (Φ := actualSlotsV2_BAUGD S) st _ _).trans ?_
      rw [hFq]
      exact hyp
    have hr1 : 3 / 5 * (Sg st * S.rho p) ≤ DP.stageRadius st (Sg st)
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) := by
      rw [← hρq]; exact hr.1
    have hr2 : DP.stageRadius st (Sg st)
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ≤
          5 / 3 * (Sg st * S.rho p) := by
      rw [← hρq]; exact hr.2
    have hpos : 0 < Sg st * S.rho p := mul_pos hsg hρ
    have hz' : ‖(actualSlotsV2_BAUGD S).stageProj st (y p) -
        (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ <
        DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) := by
      have h3 := mul_le_mul_of_nonneg_right he hρ.le
      have h4 : 3 * Sg st / 10 * S.rho p = 3 / 10 * (Sg st * S.rho p) := by ring
      linarith
    have h := adjust_sub_le_BAUGD σ hx rfl hz' (hψ _)
    have h2 : Ξs * DP.stageRadius st (Sg st)
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) ≤
        Ξs * (5 / 3 * (Sg st * S.rho p)) := mul_le_mul_of_nonneg_left hr2 hΞ
    have hexp : (5 / 3 * Ξs * Sg st + 2 * e) * S.rho p =
        Ξs * (5 / 3 * (Sg st * S.rho p)) + 2 * (e * S.rho p) := by ring
    calc _ = ‖((actualSlotsV2_BAUGD S).adjust st σ.map (y p) - y p) +
          (y p - S.boundaryOriginalMap p)‖ := by abel_nf
      _ ≤ ‖(actualSlotsV2_BAUGD S).adjust st σ.map (y p) - y p‖ +
          ‖y p - S.boundaryOriginalMap p‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · rw [adjust_eq_of_notMem_BAUGD st _ hz]
    have : e * S.rho p ≤ (5 / 3 * Ξs * Sg st + 2 * e) * S.rho p := by
      apply mul_le_mul_of_nonneg_right _ hρ.le
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 3) hΞ) hsg.le
      linarith
    linarith

/-- **The chain from its three slots** (A2-mk part (c)): for every supply with the six register
inequalities of the bindings, every `DP` over the actual v2 slot, every three slots `σ` and GAF01's
`numbers` clause at `(b_cut, b_der, κ = cutoffKappa_BAUGP2)` with `b_cut` dominating the three
cutoff constants, there is a chain on `DP` whose slots are `σ`. -/
theorem exists_chain_of_slots_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Kj : ℕ} {Ξ c cw : Fin 3 → ℝ} {bcut bder : ℝ}
    (hb0 : cutoffZeroConst_BAUGD ≤ bcut) (hb1 : cutoffOneConst_BAUGP2 ≤ bcut)
    (hb2 : cutoffTwoConst_BAUGP2 ≤ bcut)
    (hN : (∀ j, 0 < Ξ j ∧ 0 < Sg j ∧ 128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 ≤ eg j ∧
        Sg j ≤ Ξ j / 10000 ∧ 0 ≤ cw j) ∧
      5 / 3 * Ξ 0 * Sg 0 < c 0 ∧ c 0 ≤ 1 / 512 ∧
      (5 / 3 * Ξ 0 * Sg 0 * bcut * bder + Ξ 0 * bder + eg 0) < c 0 ∧
      c 0 ≤ 4 * cutoffKappa_BAUGP2 / 5 ∧ c 0 ≤ 3 * Sg 1 / 10 ∧
      (c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0)) < c 1 ∧ c 1 ≤ 1 / 512 ∧
      ((5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) * bcut * (bder + c 0) +
          Ξ 1 * (bder + c 0) + eg 1 + 2 * c 0) < c 1 ∧
      c 1 ≤ 4 * cutoffKappa_BAUGP2 / 5 ∧ c 1 ≤ 3 * Sg 2 / 10 ∧
      (c 1 + (5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1)) < c 2 ∧ c 2 ≤ 1 / 512 ∧
      ((5 / 3 * Ξ 2 * Sg 2 + (1 + Ξ 2) * c 1) * bcut * (bder + c 1) +
          Ξ 2 * (bder + c 1) + eg 2 + 2 * c 1) < c 2)
    (σ : ∀ st, BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj (Ξ st) (Sg st) (cw st)) :
    ∃ C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder
        cutoffKappa_BAUGP2, C.slot = σ := by
  have hρ := S.rho_pos
  have hv0 : 5 / 3 * Ξ 0 * Sg 0 < c 0 := hN.2.1
  have hc0 : c 0 ≤ 1 / 512 := hN.2.2.1
  have hκ0 : c 0 ≤ 4 * cutoffKappa_BAUGP2 / 5 := hN.2.2.2.2.1
  have hc0s : c 0 ≤ 3 * Sg 1 / 10 := hN.2.2.2.2.2.1
  have hv1 : c 0 + (5 / 3 * Ξ 1 * Sg 1 + (1 + Ξ 1) * c 0) < c 1 := hN.2.2.2.2.2.2.1
  have hc1 : c 1 ≤ 1 / 512 := hN.2.2.2.2.2.2.2.1
  have hκ1 : c 1 ≤ 4 * cutoffKappa_BAUGP2 / 5 := hN.2.2.2.2.2.2.2.2.2.1
  have hΞ0 := (hN.1 0).1
  have hΞ1 := (hN.1 1).1
  have hc0p : 0 ≤ c 0 := by
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) hΞ0) (hN.1 0).2.1
    linarith
  -- ψ₀
  have hB0 := S.cutoffZero_binding_of_le_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb hb0
  have hloc0 : ∀ p : W.Carrier,
      S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 0 := by
    intro p hp
    obtain ⟨q, hq, j, hj, hd, hη⟩ := hB0.2.2.2.1 p hp
    exact ⟨q, hq, mem_actualSlotsV2_stageCore_circle_BAUGD S hj hd (hη.trans (by norm_num))⟩
  have he1 : ∀ p : W.Carrier,
      ‖(actualSlotsV2_BAUGD S).adjust 0 (σ 0).map (S.boundaryOriginalMap p) -
        S.boundaryOriginalMap p‖ ≤ c 0 * S.rho p := by
    intro p
    have h := step_error_raw_BAUGD DP (σ 0) hΞ0.le (hN.1 0).2.1 hB0.2.1 S.boundaryOriginalMap
      hloc0 le_rfl (by have := (hN.1 0).2.1; positivity) (fun p => by simp) p
    have h' : (5 / 3 * Ξ 0 * Sg 0 + 2 * 0) * S.rho p ≤ c 0 * S.rho p :=
      mul_le_mul_of_nonneg_right (by linarith) (hρ p).le
    exact h.trans h'
  -- ψ₁
  have hB1 := S.cutoffOne_binding_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb
    (fun p => (actualSlotsV2_BAUGD S).adjust 0 (σ 0).map (S.boundaryOriginalMap p))
    (fun p => (he1 p).trans (mul_le_mul_of_nonneg_right hκ0 (hρ p).le))
    (edge_zm_raw_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb (σ 0) (hN.1 0).2.1 (hN.1 0).2.2.2.2.1 hloc0
      hc0p hc0 he1) hb1
  have hloc1 : ∀ p : W.Carrier,
      (actualSlotsV2_BAUGD S).adjust 0 (σ 0).map (S.boundaryOriginalMap p) ∈
        tsupport ((actualSlotsV2_BAUGD S).cutoff 1) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 1 := by
    intro p hp
    obtain ⟨q, hq, j, hj, hd, hη, ht⟩ := hB1.2.2.2.1 p hp
    exact ⟨q, hq, mem_actualSlotsV2_stageCore_edge_BAUGD S hj hd hη.le ht.le⟩
  have he2 : ∀ p : W.Carrier,
      ‖(actualSlotsV2_BAUGD S).adjust 1 (σ 1).map
          ((actualSlotsV2_BAUGD S).adjust 0 (σ 0).map (S.boundaryOriginalMap p)) -
        S.boundaryOriginalMap p‖ ≤ c 1 * S.rho p := by
    intro p
    have h := step_error_raw_BAUGD DP (σ 1) hΞ1.le (hN.1 1).2.1 hB1.2.1
      (fun p => (actualSlotsV2_BAUGD S).adjust 0 (σ 0).map (S.boundaryOriginalMap p))
      hloc1 hc0p hc0s he1 p
    have h' : (5 / 3 * Ξ 1 * Sg 1 + 2 * c 0) * S.rho p ≤ c 1 * S.rho p :=
      mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hΞ1.le hc0p]) (hρ p).le
    exact h.trans h'
  have hc1p : 0 ≤ c 1 := by
    have h5 : 0 < 5 / 3 * Ξ 1 * Sg 1 :=
      mul_pos (mul_pos (by norm_num) hΞ1) (hN.1 1).2.1
    nlinarith [mul_nonneg hΞ1.le hc0p]
  -- ψ₂
  have hB2 := S.cutoffTwo_binding_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb
    (fun p => (actualSlotsV2_BAUGD S).adjust 1 (σ 1).map
      ((actualSlotsV2_BAUGD S).adjust 0 (σ 0).map (S.boundaryOriginalMap p)))
    (fun p => (he2 p).trans (mul_le_mul_of_nonneg_right hκ1 (hρ p).le))
    (slim_zm_raw_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb (σ 0) (σ 1) (hN.1 0).2.1 (hN.1 0).2.2.2.2.1
      (hN.1 1).2.1 (hN.1 1).2.2.2.2.1 hloc0 hloc1 hc0s he1 hc1p hc1 he2) hb2
  exact ⟨⟨hN, σ, hB0, hB1, hB2⟩, rfl⟩

end DifferentialGeometry.Geometry.Collapse
