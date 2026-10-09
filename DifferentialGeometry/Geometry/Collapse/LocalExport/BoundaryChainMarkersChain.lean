import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainMarkersNear

/-!
# BCG03: (ZM) and (AM0) on the boundary chain over the v2 slot (BAUG-Dd)

Targets A3d / A3e (`TargetsBoundary-A-v3.lean.txt`; review 69 D69-5, draft 61 D61-7
`prefix_am0`, `segment_am0`): for every chain `C` on augmented data with the V3 plane specs over the
ACTUAL v2 slot and the six register inequalities of the comparability (`0 ≤ Λ`, `1 ≤ Δ`,
`10⁶ΔΛ < 10⁻⁵`, `0 ≤ V`, `0 < β 1`, `0 < b`):

* `markerCutoffW_val_BAUGD`: the W-extended marker cutoff is the stored block cutoff on `W°`;
* **`BoundaryGaf02Chain.markers_V2_BAUGD`**: markers with `ρ(c_m) < ρ(q)/16` vanish at `g₁, g₂, g₃`;
  (AM0) at every prefix `g_k` (`k = 0, …, 3`) and on the whole segment `[F_∂ p, E p]`, off the
  marker support, on all of `W`.
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

/-- The W-extended marker cutoff restricts on `W°` to the stored block cutoff of its tag. -/
theorem BoundarySupplyCore.markerCutoffW_val_BAUGD
    (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
      Λz W g δn n B oM) (m : S.MarkerIdx_BAUGC) (q : W.pieceInterior ⊤) :
    S.markerCutoffW_BAUGD m q.val = S.intCutoff_BAUGA (S.markerTag_BAUGC m) q := by
  rcases m with j | j | j
  · exact S.circleCutoffW_val_BAUGD j q
  · exact S.slimCutoffW_val_BAUGP2 j q
  · exact S.edgeCutoffW_val_BAUGP2 j q

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

include C in
/-- The positivity and size facts of the chain's budgets used by the marker kernels. -/
theorem budgets_V2_BAUGD :
    0 ≤ c 0 ∧ c 0 ≤ 1 / 512 ∧ 0 ≤ c 1 ∧ c 1 ≤ 1 / 512 ∧ 0 ≤ c 2 ∧ c 2 ≤ 1 / 512 ∧
      c 0 ≤ 3 * Sg 1 / 10 ∧ c 1 ≤ 3 * Sg 2 / 10 := by
  have hN := C.numbers
  have hv0 : 5 / 3 * Ξ 0 * Sg 0 < c 0 := hN.2.1
  have hc0p : 0 ≤ c 0 := by
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) (hN.1 0).1) (hN.1 0).2.1
    linarith
  have hc1p : 0 ≤ c 1 := by
    have h := hN.2.2.2.2.2.2.1
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) (hN.1 1).1) (hN.1 1).2.1
    nlinarith [mul_nonneg (hN.1 1).1.le hc0p]
  have hc2p : 0 ≤ c 2 := by
    have h := hN.2.2.2.2.2.2.2.2.2.2.2.1
    have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 5 / 3) (hN.1 2).1) (hN.1 2).2.1
    nlinarith [mul_nonneg (hN.1 2).1.le hc1p]
  exact ⟨hc0p, hN.2.2.1, hc1p, hN.2.2.2.2.2.2.2.1, hc2p, hN.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hN.2.2.2.2.2.1, hN.2.2.2.2.2.2.2.2.2.2.1⟩

/-- (ZM) at `g₁` and (AM0) on `[F_∂ p, g₁ p]` on the chain. -/
theorem markers_one_V2_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC),
      S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 → S.markerCLM_BAUGC m (C.g₁ q) = 0) ∧
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.g₁ p),
        |S.markerCLM_BAUGC m z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  have hN := C.numbers
  have hc := C.budgets_V2_BAUGD
  have h := markers_stage_one_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb (C.slot 0) (hN.1 0).2.1
    (hN.1 0).2.2.2.2.1 (fun p hp => C.interior_of_cutoff_zero_V2_BAUGD hp) hc.1 hc.2.1
    (fun p => by rw [← C.g₁_apply_V2_BAUGD p]; exact (C.g₁_error_lt_V2_BAUGD p).le)
  simp only [C.g₁_apply_V2_BAUGD]
  exact h

/-- (ZM) at `g₁, g₂` and (AM0) on `[F_∂ p, g₂ p]` on the chain. -/
theorem markers_two_V2_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC),
      S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 → S.markerCLM_BAUGC m (C.g₂ q) = 0) ∧
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.g₂ p),
        |S.markerCLM_BAUGC m z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  have hN := C.numbers
  have hc := C.budgets_V2_BAUGD
  have h := markers_stage_two_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb (C.slot 0) (C.slot 1) (hN.1 0).2.1
    (hN.1 0).2.2.2.2.1 (hN.1 1).2.1 (hN.1 1).2.2.2.2.1
    (fun p hp => C.interior_of_cutoff_zero_V2_BAUGD hp)
    (fun p hp => C.interior_of_cutoff_one_V2_BAUGD (by rw [C.g₁_apply_V2_BAUGD]; exact hp))
    hc.2.2.2.2.2.2.1
    (fun p => by rw [← C.g₁_apply_V2_BAUGD p]; exact (C.g₁_error_lt_V2_BAUGD p).le)
    hc.2.2.1 hc.2.2.2.1
    (fun p => by
      rw [← C.g₁_apply_V2_BAUGD p, ← C.g₂_apply_V2_BAUGD p]
      exact (C.g₂_error_lt_V2_BAUGD p).le)
  simp only [C.g₂_apply_V2_BAUGD, C.g₁_apply_V2_BAUGD]
  exact ⟨h.2.1, h.2.2⟩

/-- (ZM) at `E = g₃` and (AM0) on `[F_∂ p, E p]` on the chain. -/
theorem markers_three_V2_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    (∀ (q : W.Carrier) (m : S.MarkerIdx_BAUGC),
      S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 → S.markerCLM_BAUGC m (C.E q) = 0) ∧
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.E p),
        |S.markerCLM_BAUGC m z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  have hN := C.numbers
  have hc := C.budgets_V2_BAUGD
  have h := markers_stage_three_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb (C.slot 0) (C.slot 1) (C.slot 2)
    (hN.1 0).2.1 (hN.1 0).2.2.2.2.1 (hN.1 1).2.1 (hN.1 1).2.2.2.2.1 (hN.1 2).2.1
    (hN.1 2).2.2.2.2.1
    (fun p hp => C.interior_of_cutoff_zero_V2_BAUGD hp)
    (fun p hp => C.interior_of_cutoff_one_V2_BAUGD (by rw [C.g₁_apply_V2_BAUGD]; exact hp))
    (fun p hp => C.interior_of_cutoff_two_V2_BAUGD (by
      rw [C.g₂_apply_V2_BAUGD, C.g₁_apply_V2_BAUGD]; exact hp))
    hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
    (fun p => by rw [← C.g₁_apply_V2_BAUGD p]; exact (C.g₁_error_lt_V2_BAUGD p).le)
    (fun p => by
      rw [← C.g₁_apply_V2_BAUGD p, ← C.g₂_apply_V2_BAUGD p]
      exact (C.g₂_error_lt_V2_BAUGD p).le)
    hc.2.2.2.2.1 hc.2.2.2.2.2.1
    (fun p => by
      rw [← C.g₁_apply_V2_BAUGD p, ← C.g₂_apply_V2_BAUGD p, ← C.E_apply_V2_BAUGD p]
      exact (C.E_error_lt_V2_BAUGD p).le)
  simp only [C.E_apply_V2_BAUGD, C.g₂_apply_V2_BAUGD, C.g₁_apply_V2_BAUGD]
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- **(ZM) and (AM0) on the boundary chain** (A3d / A3e content): small markers vanish at the stage
outputs `g₁, g₂, g₃`; off the marker support, `|v_m| ≤ ρ(c_m)/32` at every prefix `g_k` and on the
segment `[F_∂ p, E p]`. -/
theorem markers_V2_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000)
    (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    (∀ (k : Fin 3) (q : W.Carrier) (m : S.MarkerIdx_BAUGC),
      S.rho (S.markerCentre_BAUGC m) < S.rho q / 16 → S.markerCLM_BAUGC m (C.stage k.succ q) = 0) ∧
    (∀ (k : Fin 4) (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      |S.markerCLM_BAUGC m (C.stage k p)| ≤ S.rho (S.markerCentre_BAUGC m) / 32) ∧
    ∀ (m : S.MarkerIdx_BAUGC) (p : W.Carrier), S.markerCutoffW_BAUGD m p = 0 →
      ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.E p),
        |S.markerCLM_BAUGC m z| ≤ S.rho (S.markerCentre_BAUGC m) / 32 := by
  have h1 := C.markers_one_V2_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb
  have h2 := C.markers_two_V2_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb
  have h3 := C.markers_three_V2_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb
  refine ⟨fun k q m hm => ?_, fun k m p hζ => ?_, h3.2⟩
  · fin_cases k
    · exact h1.1 q m hm
    · exact h2.1 q m hm
    · exact h3.1 q m hm
  · fin_cases k
    · change |S.markerCLM_BAUGC m (S.boundaryOriginalMap p)| ≤ _
      rw [S.markerCLM_boundaryOriginalMap_BAUGD, hζ, mul_zero, abs_zero]
      have := S.rho_pos (S.markerCentre_BAUGC m)
      positivity
    · exact h1.2 m p hζ _ (right_mem_segment ℝ _ _)
    · exact h2.2 m p hζ _ (right_mem_segment ℝ _ _)
    · exact h3.2 m p hζ _ (right_mem_segment ℝ _ _)

end BoundaryGaf02Chain

section Raw

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}

/-- **Consumer: BAUG-PSI's (ZM) input of `ψ₁` at the raw first stage output** (`hZM` of
`cutoffOne_binding_BAUGP2` with `f = Ψ₀ ∘ F_∂` written through the slot `σ₀`). -/
theorem edge_zm_raw_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Kj : ℕ} {Ξ₀ cw₀ : ℝ}
    (σ₀ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 0 Kj Ξ₀ (Sg 0) cw₀)
    (hsg₀ : 0 < Sg 0) (hsgΞ₀ : Sg 0 ≤ Ξ₀ / 10000)
    (hloc₀ : ∀ p : W.Carrier,
      S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 0)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) -
      S.boundaryOriginalMap p‖ ≤ E * S.rho p) :
    ∀ (j : S.EdgeIdx_BAUGD) (p : W.Carrier), S.edgeCutoffW_BAUGP2 j p = 0 →
      |S.edgeMarker_BAUGD j ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p))| ≤
        S.rho j.1 / 32 := fun j p hj =>
  (markers_stage_one_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₀ hsg₀ hsgΞ₀ hloc₀ hE hE512 hcum).2
    (.inr (.inr j)) p hj _ (right_mem_segment ℝ _ _)

/-- **Consumer: BAUG-PSI's (ZM) input of `ψ₂` at the raw second stage output** (`hZM` of
`cutoffTwo_binding_BAUGP2` with `f = Ψ₁ ∘ Ψ₀ ∘ F_∂` written through the slots). -/
theorem slim_zm_raw_BAUGD (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg)
    (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1)
    (hb : 0 < b) {Kj : ℕ} {Ξ₀ cw₀ Ξ₁ cw₁ : ℝ}
    (σ₀ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 0 Kj Ξ₀ (Sg 0) cw₀)
    (σ₁ : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData 1 Kj Ξ₁ (Sg 1) cw₁)
    (hsg₀ : 0 < Sg 0) (hsgΞ₀ : Sg 0 ≤ Ξ₀ / 10000) (hsg₁ : 0 < Sg 1) (hsgΞ₁ : Sg 1 ≤ Ξ₁ / 10000)
    (hloc₀ : ∀ p : W.Carrier,
      S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 0)
    (hloc₁ : ∀ p : W.Carrier,
      (actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) ∈
        tsupport ((actualSlotsV2_BAUGD S).cutoff 1) →
      ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ (actualSlotsV2_BAUGD S).stageCore 1)
    {e₁ : ℝ} (he₁ : e₁ ≤ 3 * Sg 1 / 10)
    (herr₁ : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p) -
      S.boundaryOriginalMap p‖ ≤ e₁ * S.rho p)
    {E : ℝ} (hE : 0 ≤ E) (hE512 : E ≤ 1 / 512)
    (hcum : ∀ p : W.Carrier, ‖(actualSlotsV2_BAUGD S).adjust 1 σ₁.map
      ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p)) -
        S.boundaryOriginalMap p‖ ≤ E * S.rho p) :
    ∀ (j : S.SlimIdx_BAUGD) (p : W.Carrier), S.slimCutoffW_BAUGP2 j p = 0 →
      |S.slimMarker_BAUGD j ((actualSlotsV2_BAUGD S).adjust 1 σ₁.map
        ((actualSlotsV2_BAUGD S).adjust 0 σ₀.map (S.boundaryOriginalMap p)))| ≤
        S.rho j.1 / 32 := fun j p hj =>
  (markers_stage_two_BAUGD DP hΛ hΔ1 hΛΔ hV hβ1 hb σ₀ σ₁ hsg₀ hsgΞ₀ hsg₁ hsgΞ₁ hloc₀ hloc₁ he₁
    herr₁ hE hE512 hcum).2.2 (.inr (.inl j)) p hj _ (right_mem_segment ℝ _ _)

end Raw

end DifferentialGeometry.Geometry.Collapse
